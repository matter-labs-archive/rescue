extern crate num_bigint;
extern crate franklin_crypto;
extern crate rand;
use num_bigint::{BigInt,ToBigInt,Sign};
use franklin_crypto::circuit::{
    num::*,
    expression::*
};
use franklin_crypto::bellman::{
    ConstraintSystem, 
    SynthesisError,
    pairing::Engine,
    LinearCombination,
    pairing::ff::{
        Field,
        PrimeField,
        PrimeFieldRepr,
        BitIterator
    }
};

pub fn rescue_hash<E, CS>(
    mut cs: CS,
    input: &[AllocatedNum<E>]
) -> Result<Vec<AllocatedNum::<E>>, SynthesisError>
    where E: Engine, CS: ConstraintSystem<E>
{
    let input_expressions={
        let mut data=vec![];
        for (i,field_element) in input.iter().enumerate(){
            data.push(Expression::from(field_element));
        }
        data
    };
    let output_expressions=generate_rescue_hash(cs.namespace(||""),input_expressions)?;
    let output_numbers = {
        let mut data=vec![];
        for (i,expr) in output_expressions.iter().enumerate(){
            data.push(expr.into_number(cs.namespace(||format!("output_{}",i)))?);
        }
        data
    };
    Ok(output_numbers)
}

pub fn generate_rescue_hash<E, CS>(
    mut cs: CS,
    mut input: Vec<Expression<E>>
) -> Result<Vec<Expression<E>>, SynthesisError>
    where E: Engine, CS: ConstraintSystem<E>
{
    //maybe, this value will be calculated
    //but it is constant for the algorithm
    let m_vecsize = 7 as usize;
    let key_size={
        let mut n=(E::Fr::NUM_BITS/2+1) as usize;
        if n<10 {n=10}
        n*2+1
    };

    let chunksize=key_size*m_vecsize;
    let len_offs=input.len() % chunksize;
    if len_offs != 0{
        input.resize(input.len()+chunksize-len_offs,Expression::constant::<CS>(E::Fr::zero()));
    }

    // Maybe some initial vector will be needed
    let mut hash=vec![Expression::constant::<CS>(E::Fr::zero());m_vecsize];

    let alpha=get_alpha::<E::Fr>();
    for (i,block) in input.chunks(chunksize).map(|a| a.to_vec()).enumerate(){
        assert_eq!(block.len(),chunksize);
        let mut key=vec![];
        for k in block.chunks(m_vecsize).map(|a| a.to_vec()){
            key.push(k);
        }
        hash=generate_rescue_round_function(cs.namespace(||format!("processing_block_{}",i)), hash, &key, &alpha)?;
    }
    Ok(hash)
}

fn generate_rescue_round_function<CS,E>(
    mut cs: CS,
    initial_hash_value: Vec<Expression<E>>,
    input_as_key:&Vec<Vec<Expression<E>>>,
    alpha: &E::Fr
)  -> Result<Vec<Expression<E>>, SynthesisError>
    where CS: ConstraintSystem<E>,E:Engine
{
    let mds=get_mds_matrix::<E::Fr>(initial_hash_value.len())?;
    assert_eq!(input_as_key.len()%2,1);
    let n_iter=(input_as_key.len()-1)/2;
    let mut hash_value=initial_hash_value;
    hash_value=add_key(hash_value,&input_as_key[0])?;
    for r in 1..=n_iter{
        let mut cs=cs.namespace(|| format!("iteration{}",r));
        for i in 0..hash_value.len(){
            let mut cs=cs.namespace(|| format!("power{}",i));
            let before=hash_value[i].into_number(&mut cs)?;
            let after=before.pow(&mut cs, alpha)?;
            hash_value[i]=Expression::from(&after);
        }
        hash_value=generate_mul_matrix_vector(&mut cs,&mds, hash_value)?;
        hash_value=add_key(hash_value, &input_as_key[r*2-1])?;
        for i in 0..hash_value.len(){
            let mut cs=cs.namespace(|| format!("root{}",i));
            let before=hash_value[i].into_number(&mut cs)?;
            let after=generate_roots(&mut cs, &before, alpha)?;
            hash_value[i]=Expression::from(&after);
        }
        hash_value=generate_mul_matrix_vector(&mut cs,&mds, hash_value)?;
        hash_value=add_key(hash_value, &input_as_key[r*2])?;
    }
    Ok(hash_value)
}
fn add_key<E:Engine>(
    input: Vec<Expression<E>>,
    key: &Vec<Expression<E>>
)  -> Result<Vec<Expression<E>>, SynthesisError>
{
    let mut output=vec![];
    for i in 0..input.len(){
        output.push(input[i].clone() + key[i].clone());
    }
    Ok(output)
}
pub fn get_mds_matrix<F:PrimeField>(m:usize)->Result<Vec<Vec<F>>,SynthesisError>{
    // https://eprint.iacr.org/2019/458.pdf 
    // pages 9-10 contain the description
    let zero=ToBigInt::to_bigint(&0).unwrap();
    let p=prime_modulus::<F>();
    let x={
        //the only requirements are
        // x_i != x_j and 
        // m - log2(m) most significant bits are zero
        // This will satisfy
        let mut res=vec![];
        for i in 1..=m{
            res.push(ToBigInt::to_bigint(&i).unwrap());
        }
        res
    };
    //the only requirement is
    // m - log2(m) most significant bits are non-zero
    // This will satisfy
    let r= &p - ToBigInt::to_bigint(&m).unwrap();

    let y={
        let mut res=vec![];
        for i in 0..m{
            res.push((&x[i] + &r) % &p);
        }
        res
    };
    //Building Cauchy matrix
    let mut res=vec![];
    for i in 0..m{
        let mut line=vec![];
        for j in 0..m{
            let element_inv=(&x[i] + &y[j]) % &p;
            let element={
                let (_,(mut el,_))=gcd(&element_inv.clone(),&p);
                while el.clone()<zero.clone() {
                    el+=&p;
                }
                el
            } % &p;
            line.push(bigint_to_fr(element).unwrap());
        }
        res.push(line);
    }
    Ok(res)
}
fn generate_mul_matrix_vector<CS,E>(
    mut cs: CS,
    matrix: &Vec<Vec<E::Fr>>,
    vector: Vec<Expression<E>>
)  -> Result<Vec<Expression<E>>, SynthesisError>
    where CS: ConstraintSystem<E>,E:Engine
{
    let mut output=vec![];
    for row in matrix{
        let mut res=Expression::constant::<CS>(E::Fr::zero());
        for (i,element) in row.iter().enumerate(){
            let val=match vector[i].get_value() {
                Some(mut curval) => {
                    curval.mul_assign(&element);    
                    Some(curval)
                }
                _ => None,
            };
            let lin_comb=LinearCombination::<E>::zero() + (element.clone(), &vector[i].lc());
            res=res + Expression::new(val,lin_comb);
        }
        output.push(res);
    }
    Ok(output)
}

fn generate_roots<CS,E>(
    mut cs: CS,
    x: &AllocatedNum<E>,
    alpha: &E::Fr
) -> Result<AllocatedNum<E>, SynthesisError>
    where CS: ConstraintSystem<E>,E:Engine
{
        //Calculate the root
        let root=AllocatedNum::alloc(cs.namespace(|| "found root"), ||{
            let zero=ToBigInt::to_bigint(&0).unwrap();
            let one=ToBigInt::to_bigint(&1).unwrap();
            let p=prime_modulus::<E::Fr>();
            let p_m_1=&p - &one;
            let (_,(anti_alpha,_))=gcd(&fr_to_bigint(alpha.clone()),&p_m_1);
            let anti_alpha={
                let mut corrected=anti_alpha;
                while corrected.clone()<zero.clone() {
                    corrected+=&p_m_1;
                }
                corrected
            } % &p_m_1;
            let a=fr_to_bigint(x.get_value().unwrap().clone());
            let res=a.modpow(&anti_alpha,&p);
            Ok(bigint_to_fr(res).unwrap())
        })?;

        {//Prove that the root is correct
            let alpha_bits_be = get_bits_be(alpha);
            let squares={
                let mut tmp:Vec<AllocatedNum<E>>=vec![root.clone()];
                for i in 1..alpha_bits_be.len(){
                    let sqr=tmp.last().unwrap().square(cs.namespace(|| format!("square{}",i)))?;
                    tmp.push(sqr);
                }
                tmp
            };
            assert_eq!(squares.len(),alpha_bits_be.len());
            let n=alpha_bits_be.len();
            let mut tmp=squares[n-1].clone();
            let last_m={
                let mut res=0;
                for i in 1..n{
                    if alpha_bits_be[i] {
                        res=i;
                    }
                }
                res
            };
            for i in 1..last_m{
                if alpha_bits_be[i] {
                    tmp=squares[n-1-i].mul(cs.namespace(|| format!("mul_due_to_bit{}",i)),&tmp)?;
                }
            }
            cs.enforce(
                || "last multiplication has to yield the argument",
                |lc| lc + tmp.get_variable(),
                |lc| lc + squares[n-1-last_m].get_variable(),
                |lc| lc + x.get_variable()
            );
    
        };
        Ok(root) 
}
fn get_alpha<F:PrimeField>() -> F{
    let zero=ToBigInt::to_bigint(&0).unwrap();
    let one=ToBigInt::to_bigint(&1).unwrap();
    let p_m_1=prime_modulus::<F>()-&one;
    let alpha={
        let mut erath=vec![ToBigInt::to_bigint(&2).unwrap(),ToBigInt::to_bigint(&3).unwrap()];
        let mut res=erath.last().unwrap().clone();
        while (&p_m_1 % &res)==zero{
            //if this prime number does not fulfill the condition gcd(alpha,p-1)=1
            //we obtain the next prime number and test it
            while {
                let mut prime=true;
                for pr in erath.iter(){
                    prime &= (&res % pr) != zero;
                }
                !prime
            } {
                res+=&one;
            }
            erath.push(res.clone());
        }
        res
    };
    bigint_to_fr(alpha).unwrap()
}

pub fn gcd(a:&BigInt,b:&BigInt)
    // gcd, (coef1, coef2)
    ->(BigInt,(BigInt,BigInt))
{
    let zero=ToBigInt::to_bigint(&0).unwrap();
    let one=ToBigInt::to_bigint(&1).unwrap();
    assert!(a.clone()>=zero.clone());
    assert!(b.clone()>zero.clone());
    if a.clone()>b.clone() {
        let (d, (x1, y1)) = gcd(b,a);
        (d,(y1,x1))
    }else{
        if a.clone()==zero.clone(){
            (b.clone(),(zero,one))
        }else{
            let (d, (x1, y1)) = gcd(&(b % a), a);
            (d,(y1 - (b / a) * x1.clone(),x1))
        }
    }
}

fn get_bits_be<F:PrimeField>(alpha:&F)->Vec<bool>{
    let mut res = Vec::with_capacity(F::NUM_BITS as usize);
    let mut found_one = false;
    for b in BitIterator::new(alpha.into_repr()) {
        found_one |= b;
        if !found_one {
            continue;
        }
        res.push(b);
    }
    res
}
pub fn prime_modulus<Fr: PrimeField>() -> BigInt {
    let mut p_repr=Fr::char();
    p_repr.sub_noborrow(&Fr::one().into_repr());
    let p_field=Fr::from_repr(p_repr).unwrap();
    let one=ToBigInt::to_bigint(&1).unwrap();
    fr_to_bigint(p_field)+&one
}
fn fr_to_bigint<Fr: PrimeField>(fr: Fr) -> BigInt {
    let mut buffer = Vec::<u8>::new();
    fr.into_repr()
        .write_be(&mut buffer)
        .expect("failed to write into Vec<u8>");
    let value = BigInt::from_bytes_be(Sign::Plus,&buffer);
    value
}
fn bigint_to_fr<F: PrimeField>(bigint: BigInt) -> Option<F> {
    F::from_str(&bigint.to_str_radix(10))
}




#[cfg(test)]
mod test {
    use franklin_crypto::{
        circuit::test::TestConstraintSystem,
        bellman::pairing::{
            bn256::{Bn256, Fr},
            ff::PrimeField
        }
    };
    use super::*;
    
    use rand::{XorShiftRng, SeedableRng, Rng};

    #[test]
    fn test_gcd(){
        let values=vec![
            (2,1,1),
            (3,1,1),(3,2,1),
            (4,1,1),(4,2,2),(4,3,1),
            (5,1,1),(5,2,1),(5,3,1),(5,4,1),
            (6,1,1),(6,2,2),(6,3,3),(6,4,2),(6,5,1),
            (7,1,1),(7,2,1),(7,3,1),(7,4,1),(7,5,1),(7,6,1),
            (8,1,1),(8,2,2),(8,3,1),(8,4,4),(8,5,1),(8,6,2),(8,7,1)
        ];
        for (a,b,d) in values{
            let big_a=ToBigInt::to_bigint(&a).unwrap();
            let big_b=ToBigInt::to_bigint(&b).unwrap();
            let big_d=ToBigInt::to_bigint(&d).unwrap();
            let (res_d,(x,y)) = gcd(&big_a, &big_b);
            assert_eq!(res_d,big_d.clone());
            assert_eq!(big_a*x + big_b*y,big_d);
        }
    }
    #[test]
    fn test_gcd2(){
        for a in 1..100{
            for b in 1..100{
                let big_a=ToBigInt::to_bigint(&a).unwrap();
                let big_b=ToBigInt::to_bigint(&b).unwrap();
                let zero=ToBigInt::to_bigint(&0).unwrap();
                let (res_d,(x,y)) = gcd(&big_a, &big_b);
                assert_eq!(&big_a % &res_d,zero.clone());
                assert_eq!(&big_b % &res_d,zero.clone());
                assert_eq!(&big_a*&x + &big_b*&y,res_d.clone());
                let (res_d1,(x1,y1)) = gcd(&big_b, &big_a);
                assert_eq!(res_d,res_d1);
                assert_eq!(&big_b*&x1 + &big_a*&y1,res_d.clone());
            }
        }
    }
    #[test]
    fn alpha_test(){
        let alpha=get_alpha::<Fr>();
        assert_eq!(alpha,Fr::from_str("5").unwrap());
    }

    #[test]
    fn root_test(){
        let alpha=get_alpha::<Fr>();
        let k=fr_to_bigint(alpha.clone());
        let values=vec!["1","2","3","4","5","6","7","8","9"];
        for x_s in values{
            let mut cs = TestConstraintSystem::<Bn256>::new();
            let x = AllocatedNum::alloc(&mut cs, || Ok(Fr::from_str(&x_s[..]).unwrap()) ).unwrap();
            let y = generate_roots(&mut cs, &x, &alpha).unwrap();

            let xx= fr_to_bigint(x.get_value().unwrap().clone());
            let yy= fr_to_bigint(y.get_value().unwrap().clone());
            assert_eq!(yy.modpow(&k,&prime_modulus::<Fr>()),xx.clone());
            assert!(cs.is_satisfied());
        }
    }


    #[test]
    fn test_full_block() {
        let mut rng = XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        let mut cs = TestConstraintSystem::<Bn256>::new();
        let input: Vec<_> = (0..128).map(|i| {
            AllocatedNum::alloc(
                cs.namespace(|| format!("input number {}", i)),
                || Ok(rng.gen())
            ).unwrap()
        }).collect();
        let hash=rescue_hash(cs.namespace(|| "Rescue_hash"),&input).unwrap();
        assert_eq!(hash.len(),7);
        assert!(cs.is_satisfied());
    }
}