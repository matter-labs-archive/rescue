extern crate num_bigint;
extern crate franklin_crypto;
use num_bigint::{BigInt,ToBigInt,Sign};
use franklin_crypto::circuit::{
    uint32::UInt32,
    multieq::MultiEq,
    boolean::Boolean,
    num::*,
    expression::Expression,
    Assignment
};
use franklin_crypto::bellman::{
    ConstraintSystem, 
    SynthesisError,
    pairing::Engine,
    LinearCombination,
    Variable,
    pairing::ff::{
        Field,
        PrimeField,
        PrimeFieldRepr,
        BitIterator
    }
};

//ToDo: choose these constants
const N_ITERATIONS:usize=16;
const M_VEC_SIZE:usize=16;

pub fn rescue_round_function<CS,E>(
    mut cs: CS,
    current_hash_value: [AllocatedNum<E>;M_VEC_SIZE],
    input_as_key:&[[AllocatedNum<E>;M_VEC_SIZE];N_ITERATIONS*2+1]
)  -> Result<[AllocatedNum<E>;M_VEC_SIZE], SynthesisError>
    where CS: ConstraintSystem<E>,E:Engine
{
    let alpha=get_alpha::<E::Fr>();
    let mut state=vec![];
    for i in 0..M_VEC_SIZE{
        state.push(Expression::from(&current_hash_value[i]));
    }
    state=add_key(state,&input_as_key[0])?;
    for r in 1..=N_ITERATIONS{
        let mut cs=cs.namespace(|| format!("iteration{}",r));
        for i in 0..M_VEC_SIZE{
            let mut cs=cs.namespace(|| format!("power{}",i));
            let before=state[i].into_number(&mut cs)?;
            let after=generate_powers(&mut cs, &before, &alpha)?;
            state[i]=Expression::from(&after);
        }
        state=generate_mds(cs.namespace(||"MDS1"), state)?;
        state=add_key(state, &input_as_key[r*2-1])?;
        for i in 0..M_VEC_SIZE{
            let mut cs=cs.namespace(|| format!("root{}",i));
            let before=state[i].into_number(&mut cs)?;
            let after=generate_roots(&mut cs, &before, &alpha)?;
            state[i]=Expression::from(&after);
        }
        state=generate_mds(cs.namespace(||"MDS2"), state)?;
        state=add_key(state, &input_as_key[r*2])?;
    }
    let mut res=current_hash_value;
    for i in 0..M_VEC_SIZE{
        res[i]=state[i].into_number(cs.namespace(|| format!("result{}",i)))?;
    }
    Ok(res)
}
fn add_key<E:Engine>(
    input: Vec<Expression<E>>,
    key: &[AllocatedNum<E>;M_VEC_SIZE]
)  -> Result<Vec<Expression<E>>, SynthesisError>
{
    let mut output=vec![];
    for i in 0..M_VEC_SIZE{
        let expr_key=Expression::from(&key[i]);
        output.push(input[i].clone() + expr_key);
    }
    Ok(output)
}
fn generate_mds<CS,E>(
    mut cs: CS,
    input: Vec<Expression<E>>
)  -> Result<Vec<Expression<E>>, SynthesisError>
    where CS: ConstraintSystem<E>,E:Engine
{
    let mut output=input;
    //ToDo: implement this transformation
    Ok(output)
}

pub fn generate_powers<CS,E>(
    mut cs: CS,
    x: &AllocatedNum<E>,
    alpha: &E::Fr
) -> Result<AllocatedNum<E>, SynthesisError>
    where CS: ConstraintSystem<E>,E:Engine
{
        assert_ne!(*alpha,E::Fr::zero());
        assert_ne!(*alpha,E::Fr::one());
        let alpha_bits_be = get_bits_be(alpha);
        let squares={//define square, square of square, etc variables
            let mut tmp:Vec<AllocatedNum<E>>=vec![x.clone()];
            //alpha is constant
            for i in 1..alpha_bits_be.len(){
                let sqr=tmp.last().unwrap().square(cs.namespace(|| format!("sqr{}",i)))?;
                tmp.push(sqr);
            }
            tmp
        };
        assert_eq!(squares.len(),alpha_bits_be.len());
        let res={
            let n=alpha_bits_be.len();
            let mut tmp=squares[n-1].clone();
            //alpha is constant
            for i in 1..n{
                if alpha_bits_be[i] {
                    tmp=squares[n-1-i].mul(cs.namespace(|| format!("mul_due_to_bit{}",i)),&tmp)?;
                }
            }
            tmp.clone()
        };
        Ok(res) 
}
pub fn generate_roots<CS,E>(
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
pub fn get_alpha<F:PrimeField>() -> F{
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
fn prime_modulus<Fr: PrimeField>() -> BigInt {
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
    fn power_test() {
        let values=vec![
            // x, a, x^a, constraints
            ("1","2","1",1),
            ("1","3","1",2),
            ("1","4","1",2),
            ("1","5","1",3),
            ("1","6","1",3),
            ("1","7","1",4),

            ("2","2","4",1),
            ("2","3","8",2),
            ("2","4","16",2),
            ("2","5","32",3),
            ("2","6","64",3),
            ("2","7","128",4),

            ("3","2","9",1),
            ("3","3","27",2),
            ("3","4","81",2),
            ("3","5","243",3),
            ("3","6","729",3),
            ("3","7","2187",4)
        ];
        for (x_s,a_s,y_s,n) in values{
            let mut cs = TestConstraintSystem::<Bn256>::new();
            let x = AllocatedNum::alloc(&mut cs, || Ok(Fr::from_str(&x_s[..]).unwrap()) ).unwrap();
            let a = Fr::from_str(&a_s[..]).unwrap();
            let y = generate_powers(&mut cs,&x,&a).unwrap();

            let xx= fr_to_bigint(x.get_value().unwrap().clone());
            let yy= fr_to_bigint(y.get_value().unwrap().clone());
            let k=fr_to_bigint(a);
            assert_eq!(xx.modpow(&k,&prime_modulus::<Fr>()),yy.clone());

            assert!(cs.is_satisfied());
            assert_eq!(cs.num_constraints(),n);
            assert_eq!(y.get_value().unwrap(),Fr::from_str(&y_s[..]).unwrap());
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

}
