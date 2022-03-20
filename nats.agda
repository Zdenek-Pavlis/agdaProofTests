
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)

+-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc′ zero n p = refl
+-assoc′ (suc m) n p rewrite +-assoc′  m n p = refl


+-identity′ : ∀ (n : ℕ) → n + zero ≡ n
+-identity′ zero = refl
+-identity′ (suc n) rewrite +-identity′ n = refl

+-suc′ : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc′ zero n = refl
+-suc′ (suc m) n rewrite +-suc′ m n = refl

+-comm′ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm′ m zero rewrite +-identity′ m = refl
+-comm′ m (suc n) rewrite +-suc′ m n | +-comm′ m n = refl


+-swap  : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap zero n p = refl
+-swap (suc m) n p
  rewrite sym ( +-assoc′  m n p)
  | sym ( +-suc′ (m + n) p)
  | +-comm′ m n
  |  ( +-assoc′ n m (suc p))
  |  +-suc′ m p   = refl



*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p = refl
*-distrib-+ (suc m) n p =  
  begin
    (suc m + n) * p 
  ≡⟨ refl ⟩
    suc( m + n) * p
  ≡⟨ refl ⟩
    p + ( m + n) * p
  ≡⟨ cong (_+_ p) (*-distrib-+ m n p) ⟩
    p + (m * p + n * p)
  ≡⟨ sym (+-assoc′ p (m * p) (n * p) ) ⟩
    p + m * p + n * p
  ≡⟨⟩
    suc m * p + n * p
  ∎

*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p = 
  begin
    ((suc m) * n) * p 
  ≡⟨ refl ⟩
    (n + (m * n)) * p
  ≡⟨ (*-distrib-+ n (m * n) p)  ⟩
    (n * p) + (m * n) * p
  ≡⟨ cong ((n * p) +_ ) ( *-assoc m n p )  ⟩
    (n * p) + m * (n * p)
  ≡⟨ refl ⟩ 
    (suc m) * (n * p)
  ∎

*-zero : ∀ (m : ℕ) → m * zero ≡ zero
*-zero zero = refl
*-zero (suc m) rewrite (*-zero m) = refl

*-suc : ∀ (m n : ℕ) → m * suc n ≡ m + (m * n)
*-suc zero n = refl
*-suc (suc m) n = 
  begin
    suc m * suc n
  ≡⟨⟩
   suc n + (m * suc n)
  ≡⟨ cong (suc n +_) (*-suc m n)  ⟩
    suc n + (m + (m * n))
  ≡⟨ sym (+-assoc′ (suc n) m (m * n)) ⟩
    (suc n + m) + (m * n) 
  ≡⟨⟩
    suc (n + m) + (m * n)
  ≡⟨ cong (_+ (m * n)) (cong (suc ) (+-comm′ n m)) ⟩
    suc (m + n) + (m * n)
  ≡⟨⟩
    suc m + n + (m * n)  
  ≡⟨ +-assoc′ (suc m) n (m * n) ⟩
    suc m + (n + (m * n))
  ≡⟨ refl ⟩
    suc m + suc m * n
  ∎

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm m zero rewrite (*-zero m) = refl
*-comm m (suc n) = 
  begin
     m * suc n
  ≡⟨ *-suc m n ⟩
    m + (m * n)
  ≡⟨ cong (m +_) (*-comm m n) ⟩
    m + n * m
  ≡⟨ refl ⟩
    suc n * m
  ∎