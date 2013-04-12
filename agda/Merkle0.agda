open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Unit
open import Data.Empty
open import Data.Sum
open import Data.Product
open import Data.Nat
open import Data.List
open import Function
open import Data.Colist hiding (_++_)

{- 
Andrew Miller  March 22 2013.

1. A record describing the parameters for an authenticated interpreter
2. A simply typed language with 3 evaluators: Identity, Prover, Verifier
3. An implementation of Hash-then-Check and a sample correctness proof

-}

module Merkle0 where

-- 1. A record with all the parameters we need for an authenticated interpreter
record Merkle0Kit : Set₁ where
  field
    D : Set                               -- A type of digests
    Data : Set                            -- A type of hashable data
    hash : Data → D                       -- Hash function
    _≟D_ : (x y : D)    → Dec (x ≡ y)     -- Decidable equality for digests
    _≟V_ : (x y : Data) → Dec (x ≡ y)     -- Decidable equality for data


{- 2. A simply typed calculus, using parametric higher-order syntax (PHOAS)
   with three provided interpretations - Identity, Prover, and Verifier.
   Special syntax is provided:
      cauth : constructs an 'auth' term from a 'data' in the host-language
      ath : constructs an arrow term from a host-function with 'data' in the
            negative position (which causes a 'check' operation to occur)
-}
module Merkle0Lang (MK : Merkle0Kit) where
  open Merkle0Kit MK
  open import Category.Monad
  open import Category.Monad.Indexed

  data Ty : Set where
    auth : Ty
    _⇒_ : Ty → Ty → Ty

  infixr 70 _⇒_

  t⟦_⟧ : Ty → Set
  t⟦ auth ⟧ = Data
  t⟦ σ ⇒ τ ⟧ = t⟦ σ ⟧ → t⟦ τ ⟧


  -- Parametric Higher Order Syntax
  data term {V : Ty → Set} : Ty → Set where
    app   : ∀ {σ τ} → term {V} (σ ⇒ τ) → term {V} σ → term τ
    lam   : ∀ {σ τ} → (V σ → term {V} τ) → term (σ ⇒ τ)
    var   : ∀ {τ} → V τ → term τ
    ath   : ∀ {τ} → (Data → term {V} τ) → term (auth ⇒ τ)
    cauth : Data → term auth

  {- Final form of VTerm ... parametric in type of Vars -}
  Term : Ty → Set₁
  Term t = ∀ {V} → term {V} t


  {- Identity default denotation -}
  ⟦_⟧ : ∀ {τ} → term τ → t⟦ τ ⟧
  ⟦ var x ⟧ = x
  ⟦ cauth x ⟧ = x
  ⟦ app t x ⟧ = ⟦ t ⟧ ⟦ x ⟧
  ⟦ lam x ⟧ = λ z → ⟦ x z ⟧
  ⟦ ath x ⟧ = λ z → ⟦ x z ⟧

  MP' : Set → Set
  MP' a = List Data × a
  RawPMonad : RawMonad MP'
  RawPMonad = record
    { _>>=_ = {!!}
    ; return = {!!}
    }

  MV' : Set → Set
  MV' a = List Data → ⊤ ⊎ List Data × a
  RawVMonad : RawMonad MV'
  RawVMonad = record
    { _>>=_ = {!!}
    ; return = {!!}
    }  

  t⟦_⟧P' : Ty → Set
  t⟦ τ ⟧P' = MP' (f τ) where
    f : Ty → Set
    f auth = Data
    f (τ₁ ⇒ τ₂) = t⟦ τ₁ ⟧P' → MP' t⟦ τ₂ ⟧P'

  t⟦_⟧V' : Ty → Set
  t⟦ τ ⟧V' = MV' (f τ) where
    f : Ty → Set
    f auth = D
    f (τ₁ ⇒ τ₂) = t⟦ τ₁ ⟧V' → MV' t⟦ τ₂ ⟧V'

  prop_correct : ∀ {τ : Ty} → t⟦ τ ⟧V' → t⟦ τ ⟧P' → t⟦ τ ⟧ → Set
  prop_correct {auth} v (vo , dat) c = v vo ≡ inj₂ ([] , hash dat) × dat ≡ c
  prop_correct {τ ⇒ τ₁} mv mp c = ∀ v' p' c' → prop_correct {τ} v' p' c' → 
    prop_correct {τ₁} (RawMonad._>>=_ RawVMonad mv (λ f → RawMonad.join RawVMonad (f v')))
                      (RawMonad._>>=_ RawPMonad mp (λ f → RawMonad.join RawPMonad (f p')))
                      (c c')

  collision : Set
  collision = ∃ (λ {(x , y) → x ≢ y × hash x ≡ hash y})

  prop_sound : ∀ {τ : Ty} → t⟦ τ ⟧V' → t⟦ τ ⟧ → Set
  prop_sound {auth} v c = (vo : List Data) → v vo ≡ inj₂ ([] , hash c)
                                           ⊎ v vo ≡ inj₁ tt
                                           ⊎ collision
  prop_sound {τ ⇒ τ₁} mv c = ∀ v' c' → prop_sound {τ} v' c' → 
      prop_sound {τ₁} (RawMonad._>>=_ RawVMonad mv (λ f → RawMonad.join RawVMonad (f v')))
                      (c c')

  record AuthLanguage : Set₁ where
    field
      Term' : Ty → Set
      ⟦_⟧' : ∀ {τ} → Term' τ → t⟦ τ ⟧
      ⟦_⟧P : ∀ {τ} → Term' τ → t⟦ τ ⟧P'
      ⟦_⟧V : ∀ {τ} → Term' τ → t⟦ τ ⟧V'

      correct : {τ : Ty} → (t : Term' τ) → prop_correct {τ} ⟦ t ⟧V ⟦ t ⟧P ⟦ t ⟧'

  record RawAuthMonad : Set₁ where
    field
      Q : Set
      M : Set → Set
      monad_ : RawMonad M
      check : Q → M Data
      place : Data → M Q

    open RawMonad monad_ public

  {- Denotation in terms of Monad -}
  module Denote (Mon : RawAuthMonad) where
    open RawAuthMonad Mon

    t⟦_⟧m : Ty → Set
    t⟦ τ ⟧m = M (f τ) where
      f : Ty → Set
      f auth = Q
      f (τ₁ ⇒ τ₂) = t⟦ τ₁ ⟧m → M (t⟦ τ₂ ⟧m)

    ⟦_⟧m : ∀ {τ} → term τ → t⟦ τ ⟧m
    ⟦ cauth x ⟧m = place x
    ⟦ var x ⟧m = x
    ⟦ app t t₁ ⟧m = ⟦ t ⟧m >>= λ f → join (f ⟦ t₁ ⟧m)
    ⟦ ath f ⟧m = return (λ md → md >>= λ d → check d >>= λ dat → return ⟦ f dat ⟧m)
    ⟦ lam f ⟧m = return (λ x → return ⟦ f x ⟧m)

  {- Prover section -}

  Prover : RawAuthMonad
  Prover = record
    { M = λ a → List Data × a
    ; Q = Data
    ; monad_ = record 
      { _>>=_ = λ ma f → (proj₁ ma) ++ proj₁ (f (proj₂ ma)) , proj₂ (f (proj₂ ma))
      ; return = ret'
      }
    ; check = λ dat → Data.List.[_] dat , dat
    ; place = ret'
    } 
    where 
      ret' : ∀ {a} → a → List Data × a
      ret' a = [] , a

  t⟦_⟧P : Ty → Set
  t⟦_⟧P = Denote.t⟦_⟧m Prover

  ⟦_⟧P : ∀ {τ} → term τ → t⟦ τ ⟧P
  ⟦_⟧P = Denote.⟦_⟧m Prover


  {- Examples -}
  postulate
    _⊕_ : Data → Data → Data   -- Assume we have a 'plus' operation on data

  ttplus : Term (auth ⇒ auth ⇒ auth)
  ttplus = ath (λ x → ath (λ y → cauth (x ⊕ y)))

  f : t⟦ auth ⇒ auth ⇒ auth ⟧P
  f = ⟦ ttplus ⟧P

  {- Verifier section -}

  Verifier : RawAuthMonad
  Verifier = record
    { M = M
    ; Q = D
    ; monad_ = record
      { _>>=_ = bind'
      ; return = ret'
      }
    ; check = check
    ; place = ret' ∘ hash
    } where
      M : Set → Set
      M = λ a → List Data → ⊤ ⊎ List Data × a
      ret' : ∀ {a} → a → M a
      ret' a = λ vo → inj₂ (vo , a)
      bind' : ∀ {a b} → M a → (a → M b) → M b
      bind' ma f vo with ma vo
      ... | inj₂ (vo' , a) = f a vo'
      ... | inj₁ tt = inj₁ tt
      check : D → M Data
      check dig [] = inj₁ tt
      check dig (dat ∷ vo) with hash dat ≟D dig
      ... | yes _ = inj₂ (vo , dat)
      ... | no  _ = inj₁ tt

  t⟦_⟧V : Ty → Set
  t⟦_⟧V = Denote.t⟦ Verifier ⟧m

  ⟦_⟧V : ∀ {τ} → term τ → t⟦ τ ⟧V
  ⟦_⟧V = Denote.⟦ Verifier ⟧m


  runP : Term auth → List Data × t⟦ auth ⟧
  runP t = ⟦ t ⟧P

  -- 

{-
Definition (Lat): Let τ and 
  Types: by induction
         including a base type
         and including meta-language arrows
  Terms: by induction
  
-}
  lem-correct : ∀ {τ : Ty} → t⟦ τ ⟧V → t⟦ τ ⟧P → t⟦ τ ⟧ → Set
  lem-correct {auth} v (vo , dat) c = v vo ≡ inj₂ ([] , hash dat) × dat ≡ c
  lem-correct {τ ⇒ τ₁} mv mp c = ∀ v' p' c' → lem-correct {τ} v' p' c' → 
    lem-correct {τ₁} (RawAuthMonad._>>=_ Verifier mv (λ f → RawAuthMonad.join Verifier (f v')))
                     (RawAuthMonad._>>=_ Prover   mp (λ f → RawAuthMonad.join Prover   (f p')))
                     (c c')

--  postulate
--    paramet : (f : ∀ (a : Set) ∀ (a : Set) (ȧ : a → Set) (x : a)  {!!}

--  paramet : ∀ X τ (V : Ty → Set) (f : term τ → X) (t : Term τ) → t {f V} ≡ f (t (f V))
--  paramet = {!!}

  pf-correct : ∀ {τ : Ty} (t : Term τ) → lem-correct {τ} ⟦ t ⟧V ⟦ t ⟧P ⟦ t ⟧
  pf-correct = {!!}





-- 3. A simple example of the core 'hash-then-check' computation along
-- with a soundness/correctness proof
module HashThenCheck (MK : Merkle0Kit) where
  open Merkle0Kit MK

  verify : D × Data → ⊤ ⊎ Data
  verify (d , vo) with d ≟D hash vo
  ... | yes _ = inj₂ vo
  ... | no  _ = inj₁ tt

  correct : ∀ d → verify (hash d , d) ≡ inj₂ d
  correct d with hash d ≟D hash d
  ... | yes _ = refl
  ... | no ¬p = ⊥-elim (¬p refl)

  collision : Set
  collision = ∃ (λ {(x , y) → x ≢ y × hash x ≡ hash y})

  sound : ∀ d vo → collision ⊎
                   verify (hash d , vo) ≡ inj₂ d ⊎
                   verify (hash d , vo) ≡ inj₁ tt                   
  sound d vo with hash d ≟D hash vo | d ≟V vo
  ... | yes p | yes q = inj₂ (inj₁ (sym (cong inj₂ q)))
  ... | yes p | no ¬q = inj₁ ((d , vo) , ¬q , p)
  ... | no ¬p | no ¬q = inj₂ (inj₂ refl)
  ... | no ¬p | yes q = ⊥-elim (¬p (cong hash q))



