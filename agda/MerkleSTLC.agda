open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Unit
open import Data.Empty
open import Data.Sum
open import Data.Product
open import Data.Nat
open import Data.List
open import Data.Bool
open import Function
open import Data.Colist hiding (_++_)


module MerkleSTLC where

postulate Data : Set
  
mutual
  data Ty : Set where
    One : Ty
    _⊗_ : Ty → Ty → Ty
    _⊕_ : Ty → Ty → Ty
    _⇒_ : Ty → Ty → Ty
    _●_ : (τ : Ty) → Wf● τ → Ty
  dTy : Set
  dTy = Σ Ty Wf●
  data Wf● : Ty → Set where
    wfOne : Wf● One
    wf⊕ : ∀ {τ₀ τ₁} → Wf● τ₀ → Wf● τ₁ → Wf● (τ₀ ⊕ τ₁)
    wf⊗ : ∀ {τ₀ τ₁} → Wf● τ₀ → Wf● τ₁ → Wf● (τ₀ ⊗ τ₁)
    wf● : ∀ {τ} → (wf : Wf● τ) → Wf● (τ ● wf)

infixr 70 _⇒_

record Merkle0Kit : Set₁ where
  field
    D : Set
    hash : Data → D                       -- Hash function
    _≟D_ : (x y : D)    → Dec (x ≡ y)     -- Decidable equality for digests
    _≟V_ : (x y : Data) → Dec (x ≡ y)     -- Decidable equality for data

data Con : Set where
  ε : Con
  _⊙_ : Con -> Ty -> Con

data Var : (Γ : Con) (σ : Ty) → Set where
  zero : ∀ {Γ σ} → Var (Γ ⊙ σ) σ
  suc : ∀ {Γ σ τ} → Var Γ τ → Var (Γ ⊙ σ) τ

data Env {Val : Ty → Set} : Con → Set where
  ε : Env ε
  _::_ : ∀ {Γ σ} → Val σ → Env {Val} Γ → Env (Γ ⊙ σ)

_!!_ : ∀ {Val Γ σ} → Env {Val} Γ → Var Γ σ → Val σ
(x :: ρ) !! zero = x
(x :: ρ) !! suc x₁ = ρ !! x₁


module Merkle0Lang (MK : Merkle0Kit) where
  open Merkle0Kit MK


  data Term : Con → Ty → Set where
    var   : ∀ {Γ τ} → Var Γ τ → Term Γ τ
    lam   : ∀ {Γ σ τ} → Term (Γ ⊙ σ) τ → Term Γ (σ ⇒ τ)
    app   : ∀ {Γ σ τ} → Term Γ (σ ⇒ τ) → Term Γ σ → Term Γ τ
    auth  : ∀ {Γ τ} → Term Γ τ → (wf : Wf● τ) → Term Γ (τ ● wf)



  open import Category.Monad
  open import Category.Monad.Indexed

  -- General form of type denotation (parameterized by a monad and a functor)
  t⟦_⟧d_∥_ : Ty → (Set → Set) → (Set → Set) → Set
  t⟦ One ⟧d M ∥ f = Unit
  t⟦ τ ● wf ⟧d M ∥ f = f (t⟦ τ ⟧d M ∥ f)
  t⟦ τ₁ ⇒ τ₂ ⟧d M ∥ f = M (t⟦ τ₁ ⟧d M ∥ f) → M (t⟦ τ₂ ⟧d M ∥ f)
  t⟦ τ₀ ⊕ τ₁ ⟧d M ∥ f = t⟦ τ₀ ⟧d M ∥ f ⊎ t⟦ τ₁ ⟧d M ∥ f
  t⟦ τ₀ ⊗ τ₁ ⟧d M ∥ f = t⟦ τ₀ ⟧d M ∥ f × t⟦ τ₁ ⟧d M ∥ f

  record AuthModel : Set₁ where
    field
      M : Set → Set
      monad_ : RawMonad M

      -- This field is meant to express the everything needed to specialize
      -- the denotation-type function for authenticated types for Prover/Verifier.
      -- Roughly, identity should treat it as a fixpoint... or structurally recursive call?
      -- Verifier uses only a constant D and no need to recurse (constant functor)
      -- Prover pairs the fixpoint with a D
      tt⟦_⟧m : Set → Set
      check : ∀ {τ} {wf : Wf● τ} → t⟦ τ ● wf ⟧d M ∥ tt⟦_⟧m → M (t⟦ τ ⟧d M ∥ tt⟦_⟧m)
      place : ∀ {τ} → (wf : Wf● τ) → t⟦ τ ⟧d M ∥ tt⟦_⟧m → t⟦ τ ● wf ⟧d M ∥ tt⟦_⟧m

    open RawMonad monad_ public

  {- Denotation in parameterized by an AuthModel -}
  module Denote (Mon : AuthModel) where
    open AuthModel Mon

    ttm : Ty → Set
    ttm τ = t⟦ τ ⟧d M ∥ tt⟦_⟧m

    ⟦_⟧m : ∀ {Γ τ} → Term Γ τ → Env {M ∘ ttm} Γ → M (ttm τ)
    ⟦ var i ⟧m ρ = ρ !! i
    ⟦ lam f ⟧m ρ = return (λ x → x >>= λ x' → ⟦ f ⟧m (return x' :: ρ))
    ⟦ app t t₁ ⟧m ρ = ⟦ t ⟧m ρ >>= λ f → f (⟦ t₁ ⟧m ρ)
    ⟦ auth t wf ⟧m ρ = ⟦ t ⟧m ρ >>= return ∘ place wf

  Identity : AuthModel
  Identity = record
    { M = id
    ; monad_ = record 
      { _>>=_ = λ ma f → f ma
      ; return = id
      }
    ; tt⟦_⟧m = id
    ; check = id
    ; place = λ wf → id
    }

  t⟦_⟧I : Ty → Set
  t⟦_⟧I = Denote.ttm Identity

  ⟦_⟧I : ∀ {Γ τ} → Term Γ τ → Env {t⟦_⟧I} Γ → t⟦ τ ⟧I
  ⟦_⟧I = Denote.⟦_⟧m Identity

  tM⟦_⟧I : Ty → Set
  tM⟦_⟧I = AuthModel.M Identity ∘ t⟦_⟧I


  {- Prover section -}

  Prover : AuthModel
  Prover = record
    { M = λ a → List Data × a
    ; monad_ = record 
      { _>>=_ = λ ma f → (proj₁ ma) ++ proj₁ (f (proj₂ ma)) , proj₂ (f (proj₂ ma))
      ; return = ret'
      }
    ; tt⟦_⟧m = ttm
    ; check = λ dat → {!!} --Data.List.[_] dat × {!!} --dat
    ; place = {!!} ret'
    }
    where
      ttm : Set → Set
      ttm = λ x → D × x
      ret' : ∀ {a} → a → List Data × a
      ret' a = [] , a

  t⟦_⟧P : Ty → Set
  t⟦_⟧P = Denote.ttm Prover

  tM⟦_⟧P : Ty → Set
  tM⟦_⟧P = AuthModel.M Prover ∘ t⟦_⟧P

  ⟦_⟧P : ∀ {Γ τ} → Term Γ τ → Env {tM⟦_⟧P} Γ → tM⟦ τ ⟧P
  ⟦_⟧P t ρ = Denote.⟦_⟧m Prover t ρ


  {- Verifier section -}

  Verifier : AuthModel
  Verifier = record
    { M = M
    ; monad_ = record
      { _>>=_ = bind'
      ; return = ret'
      }
    ; check = {!!}
    ; place = {!!} --ret' ∘ hash
    ; tt⟦_⟧m = λ _ → D
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
  t⟦_⟧V = Denote.ttm Verifier

  tM⟦_⟧V : Ty → Set
  tM⟦_⟧V = AuthModel.M Verifier ∘ t⟦_⟧V

  ⟦_⟧V : ∀ {Γ τ} → Term Γ τ → Env {tM⟦_⟧V} Γ → tM⟦ τ ⟧V
  ⟦_⟧V = Denote.⟦_⟧m Verifier


  {- Data conversions for auth-types -}

  shallow : ∀ {τ} {wf : Wf● τ} → t⟦ τ ⟧P → t⟦ τ ⟧V
  shallow = {!!}

  hash-s : ∀ {τ} {wf : Wf● τ} → t⟦ τ ⟧V → D
  hash-s = {!!}

  merkleize : ∀ {τ} → (wf : Wf● τ) → t⟦ τ ⟧I → t⟦ τ ⟧P
  merkleize {One} _ ⊤ = ⊤
  merkleize {τ ⊗ τ₁} (wf⊗ wf₀ wf₁) (x , y) = merkleize wf₀ x , merkleize wf₁ y
  merkleize {τ ⊕ τ₁} (wf⊕ wf₀ _) (inj₁ x) = inj₁ (merkleize wf₀ x)
  merkleize {τ ⊕ τ₁} (wf⊕ _ wf₁) (inj₂ y) = inj₂ (merkleize wf₁ y)
  merkleize {τ ⇒ τ₁} () _
  merkleize {τ ● ._} (wf● wf) i with merkleize wf i
  ... | m = hash-s {τ} {wf} (shallow {τ} {wf} m) , m



  {- Correctness Relations -}

  mutual
    rel-correct : {τ : Ty} → t⟦ τ ⟧V → t⟦ τ ⟧I → t⟦ τ ⟧P → Set
    rel-correct {One} v i p = ⊤
    rel-correct {τ₀ ⊗ τ₁} (v₀ , v₁) (i₀ , i₁) (p₀ , p₁) = rel-correct {τ₀} v₀ i₀ p₀ × rel-correct {τ₁} v₁ i₁ p₁
    rel-correct {τ₀ ⊕ τ₁} (inj₁ v) (inj₁ i) (inj₁ p) = rel-correct {τ₀} v i p
    rel-correct {τ₀ ⊕ τ₁} (inj₂ v) (inj₂ i) (inj₂ p) = rel-correct {τ₁} v i p
    rel-correct {τ₀ ⊕ τ₁} _ _ _ = ⊥
    rel-correct {τ₀ ⇒ τ₁} v i p = ∀ {v'} {i'} {p'} → rel-correct {τ₀} v' i' p' → m-rel-correct {τ₁} (v (AuthModel.return Verifier v')) (i i') (p (AuthModel.return Prover p'))
    rel-correct {τ ● wf} v i p = p ≡ merkleize {τ ● wf} (wf● wf) i × hash-s {τ ● wf} {wf● wf} (shallow {τ ● wf} {wf● wf} p) ≡ v

    m-rel-correct : {τ : Ty} → tM⟦ τ ⟧V → tM⟦ τ ⟧I → tM⟦ τ ⟧P → Set
    m-rel-correct {τ} v i (vo , p) = ∀ rest → rel' rest (v (vo ++ rest)) where
      rel' : List Data → ⊤ ⊎ List Data × t⟦ τ ⟧V → Set
      rel' _ (inj₁ ⊤) = ⊥
      rel' rest (inj₂ (vo' , v')) = vo' ≡ rest × rel-correct {τ} v' i p

  collision : Set
  collision = ∃ (λ {(x , y) → x ≢ y × hash x ≡ hash y})



  {- Correctness Proof -}

  correct-ty : Ty → Set
  correct-ty τ = ∃ λ v → ∃ λ i → ∃ λ p → m-rel-correct {τ} v i p

  projectV : ∀ {Γ} → Env {correct-ty} Γ → Env {tM⟦_⟧V} Γ
  projectV ε = ε
  projectV ((v , _ , _ , _) :: Γ) = v :: projectV Γ

  projectI : ∀ {Γ} → Env {correct-ty} Γ → Env {t⟦_⟧I} Γ
  projectI ε = ε
  projectI ((_ , i , _ , _) :: Γ) = i :: projectI Γ

  projectP : ∀ {Γ} → Env {correct-ty} Γ → Env {tM⟦_⟧P} Γ
  projectP ε = ε
  projectP ((_ , _ , p , _) :: Γ) = p :: projectP Γ

  pf-correct : ∀ {Γ τ} (t : Term Γ τ) → (ρ : Env {correct-ty} Γ) → m-rel-correct {τ} (⟦_⟧V {Γ} {τ} t (projectV ρ)) (⟦_⟧I {Γ} {τ} t (projectI ρ)) (⟦_⟧P {Γ} {τ} t (projectP ρ))
  pf-correct {Γ} {τ} t ρ with (⟦ t ⟧V (projectV ρ)) | (⟦ t ⟧I (projectI ρ)) | (⟦ t ⟧P (projectP ρ))
  pf-correct {Γ} {τ} (var x) ρ | v | i | p = {!!}
  pf-correct (lam t) ρ | v | i | p = {!!}
  pf-correct (app t t₁) ρ | v | i | p = {!!}
  pf-correct (auth t wf) ρ | v | i | p = {!!}

  pf-correctP : ∀ {Γ τ} (t : Term Γ τ) → Env {correct-ty} Γ → correct-ty τ
  pf-correctP t ρ with (⟦ t ⟧V (projectV ρ)) | (⟦ t ⟧I (projectI ρ)) | (⟦ t ⟧P (projectP ρ))
  pf-correctP (var i) ρ | _ | _ | _ = ρ !! i
  pf-correctP {_} {τ₁ ⇒ τ₂} (lam f) ρ | v | i | p = ⟦ lam f ⟧V (projectV ρ) , ⟦ lam f ⟧I (projectI ρ) , ⟦ lam f ⟧P (projectP ρ) , {!!}
  pf-correctP (app t t₁) ρ | v | i | p = {!!}
  pf-correctP {_} {τ ● wf} (auth x ._) ρ | v | i | p = ⟦ auth x wf ⟧V (projectV ρ) , ⟦ auth x wf ⟧I (projectI ρ) , ⟦ auth x wf ⟧P (projectP ρ) , {!!}
