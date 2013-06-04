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
  

mutual
  data Ty : Set where
    One : Ty
    _⊗_ : Ty → Ty → Ty
    _⊕_ : Ty → Ty → Ty
    _⇒_ : Ty → Ty → Ty
    _●_ : (τ : Ty) → .(Wf● τ) → Ty
  data Wf● : Ty → Set where
    wfOne : Wf● One
    wf⊕ : ∀ {τ₀ τ₁} → Wf● τ₀ → Wf● τ₁ → Wf● (τ₀ ⊕ τ₁)
    wf⊗ : ∀ {τ₀ τ₁} → Wf● τ₀ → Wf● τ₁ → Wf● (τ₀ ⊗ τ₁)
    wf● : ∀ {τ} → (wf : Wf● τ) → Wf● (τ ● wf)


infixr 70 _⇒_

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



_≟T_ : (x y : Ty) → Dec (x ≡ y)     -- Decidable equality for types
One ≟T One = yes refl
One ≟T (v ⊗ v₁) = no (λ ())
One ≟T (v ⊕ v₁) = no (λ ())
One ≟T v ⇒ v₁ = no (λ ())
One ≟T (v ● x) = no (λ ())
(x ⊗ x₁) ≟T y = {!!}
(x ⊕ x₁) ≟T y = {!!}
x ⇒ x₁ ≟T y = {!!}
(x ● x₁) ≟T y = {!!}

Shal : (D : Set) → (τ : Ty) → (wf : Wf● τ) → Set
Shal D (One) (wf) = Unit
Shal D (τ₀ ⊗ τ₁) (wf⊗ wf₀ wf₁) = Shal D (τ₀) (wf₀) × Shal D (τ₁) (wf₁)
Shal D (τ₀ ⊕ τ₁) (wf⊕ wf₀ wf₁) = Shal D (τ₀) (wf₀) ⊎ Shal D (τ₁) (wf₁)
Shal D (τ ⇒ τ₁) (())
Shal D (τ ● _) (wf) = D

record MerkleKit : Set₁ where
  field
    D : Set
    _≟D_ : (x y : D) → Dec (x ≡ y)     -- Decidable equality for digests
    hash : ∀ {τ} {wf} → Shal D τ wf → D

module Merkle0Lang (MK : MerkleKit) where
  open MerkleKit MK

  Shallow : (τ : Ty) → (wf : Wf● τ) → Set
  Shallow = Shal D

  irrel : ∀ {τ} (x y : Wf● τ) → x ≡ y
  irrel {One} wfOne wfOne = refl
  irrel {τ ⊗ τ₁} (wf⊗ x x₁) (wf⊗ y y₁) = cong₂ wf⊗ (irrel x y) (irrel x₁ y₁)
  irrel {τ ⊕ τ₁} (wf⊕ x x₁) (wf⊕ y y₁) = cong₂ wf⊕ (irrel x y) (irrel x₁ y₁)
  irrel {τ ⇒ τ₁} () ()
  irrel {τ ● _} (wf● _) (wf● _) = refl

  eq-shal : ∀ {τ τ' wf wf'} → τ ≡ τ' → Shallow τ wf ≡ Shallow τ' wf'
  eq-shal {τ} {.τ} {wf} {wf'} refl = cong (Shallow τ) (irrel wf wf')

  VO : Set
  VO = Σ Ty λ τ → Σ (Wf● τ) λ wf → Shallow τ wf

  data Term : Con → Ty → Set where
    var   : ∀ {Γ τ} → Var Γ τ → Term Γ τ
    lam   : ∀ {Γ σ τ} → Term (Γ ⊙ σ) τ → Term Γ (σ ⇒ τ)
    app   : ∀ {Γ σ τ} → Term Γ (σ ⇒ τ) → Term Γ σ → Term Γ τ
    auth  : ∀ {Γ τ} → Term Γ τ → (wf : Wf● τ) → Term Γ (τ ● wf)

  -- General form of type denotation (parameterized by a monad and a functor)
  t⟦_⟧d_∥_ : Ty → (Set → Set) → (Set → Set) → Set
  t⟦ One ⟧d M ∥ f = Unit
  t⟦ τ ● wf ⟧d M ∥ f = f (t⟦ τ ⟧d M ∥ f)
  t⟦ τ₁ ⇒ τ₂ ⟧d M ∥ f = M (t⟦ τ₁ ⟧d M ∥ f) → M (t⟦ τ₂ ⟧d M ∥ f)
  t⟦ τ₀ ⊕ τ₁ ⟧d M ∥ f = t⟦ τ₀ ⟧d M ∥ f ⊎ t⟦ τ₁ ⟧d M ∥ f
  t⟦ τ₀ ⊗ τ₁ ⟧d M ∥ f = t⟦ τ₀ ⟧d M ∥ f × t⟦ τ₁ ⟧d M ∥ f

  Mv Mi Mp : Set → Set
  Mv a = List VO → Unit ⊎ List VO × a
  Mi a = a
  Mp a = List VO × a

  Fv Fi Fp : Set → Set
  Fv a = D
  Fi a = a
  Fp a = D × a

  {- Data conversions for auth-types -}

  t⟦_⟧V t⟦_⟧I t⟦_⟧P : Ty → Set
  t⟦ τ ⟧V = t⟦ τ ⟧d Mv ∥ Fv
  t⟦ τ ⟧I = t⟦ τ ⟧d Mi ∥ Fi
  t⟦ τ ⟧P = t⟦ τ ⟧d Mp ∥ Fp

  tM⟦_⟧V tM⟦_⟧I tM⟦_⟧P : Ty → Set
  tM⟦_⟧V = Mv ∘ t⟦_⟧V
  tM⟦_⟧I = Mi ∘ t⟦_⟧I
  tM⟦_⟧P = Mp ∘ t⟦_⟧P

  VO-iso : ∀ {τ} {wf : Wf● τ} → Shallow τ wf ≡ t⟦ τ ⟧V
  VO-iso {One} {wf} = refl
  VO-iso {τ₀ ⊗ τ₁} {wf⊗ wf₀ wf₁} = cong₂ _×_ (VO-iso {τ₀} {wf₀}) (VO-iso {τ₁} {wf₁})
  VO-iso {τ₀ ⊕ τ₁} {wf⊕ wf₀ wf₁} = cong₂ _⊎_ (VO-iso {τ₀} {wf₀}) (VO-iso {τ₁} {wf₁})
  VO-iso {τ ⇒ τ₁} {()}
  VO-iso {τ ● x} = refl

  shallow : ∀ {τ} {wf : Wf● τ} → t⟦ τ ⟧P → t⟦ τ ⟧V
  shallow {One} {wf} v = v
  shallow {τ₀ ⊗ τ₁} {wf⊗ wf₀ wf₁} (v₀ , v₁) = shallow {τ₀} {wf₀} v₀ , shallow {τ₁} {wf₁} v₁
  shallow {τ₀ ⊕ τ₁} {wf⊕ wf₀ wf₁} (inj₁ x) = inj₁ (shallow {τ₀} {wf₀} x)
  shallow {τ₀ ⊕ τ₁} {wf⊕ wf₀ wf₁} (inj₂ y) = inj₂ (shallow {τ₁} {wf₁} y)
  shallow {τ₀ ⇒ τ₁} {()} _
  shallow {τ ● _} {wf● wf} (d , v) = d

  hash-s : ∀ {τ} {wf : Wf● τ} → t⟦ τ ⟧V → D
  hash-s {τ} {wf} x = hash {τ} {wf} (subst id (sym (VO-iso {τ} {wf})) x)

  merkleize : ∀ {τ} {wf : Wf● τ} → t⟦ τ ⟧I → t⟦ τ ⟧P
  merkleize {One} {_} Unit = Unit
  merkleize {τ ⊗ τ₁} {wf⊗ wf₀ wf₁} (x , y) = merkleize {τ} {wf₀} x , merkleize {τ₁} {wf₁} y
  merkleize {τ ⊕ τ₁} {wf⊕ wf₀ _} (inj₁ x) = inj₁ (merkleize {τ} {wf₀} x)
  merkleize {τ ⊕ τ₁} {wf⊕ _ wf₁} (inj₂ y) = inj₂ (merkleize {τ₁} {wf₁} y)
  merkleize {τ ⇒ τ₁} {()} _
  merkleize {τ ● _} {wf● wf} i with merkleize {τ} {wf} i
  ... | m = hash-s {τ} {wf} (shallow {τ} {wf} m) , m


  {- AuthModel -}

  open import Category.Monad
  open import Category.Monad.Indexed

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

  ⟦_⟧I : ∀ {Γ τ} → Term Γ τ → Env {t⟦_⟧I} Γ → t⟦ τ ⟧I
  ⟦_⟧I = Denote.⟦_⟧m Identity


  {- Prover section -}

  Prover : AuthModel
  Prover = record
    { M = Mp
    ; monad_ = record 
      { _>>=_ = λ ma f → (proj₁ ma) ++ proj₁ (f (proj₂ ma)) , proj₂ (f (proj₂ ma))
      ; return = ret'
      }
    ; tt⟦_⟧m = Fp
    ; check = check'
    ; place = place'
    }
    where
      ret' : ∀ {a} → a → List VO × a
      ret' a = [] , a
      check' : ∀ {τ} {wf : Wf● τ} → t⟦ τ ● wf ⟧P → tM⟦ τ ⟧P
      check' {τ} {wf} (d , v) = Data.List.[] , v --Data.List.[ shallow {τ} {wf} v ] , {!!} --dat
      place' : ∀ {τ} {wf : Wf● τ} → t⟦ τ ⟧P → tM⟦ τ ● wf ⟧P
      place' {τ} {wf} v = Data.List.[] , (hash-s {τ} {wf} (shallow {τ} {wf} v) , v)

  ⟦_⟧P : ∀ {Γ τ} → Term Γ τ → Env {tM⟦_⟧P} Γ → tM⟦ τ ⟧P
  ⟦_⟧P t ρ = Denote.⟦_⟧m Prover t ρ


  {- Verifier section -}

  Verifier : AuthModel
  Verifier = record
    { M = Mv
    ; monad_ = record
      { _>>=_ = bind'
      ; return = ret'
      }
    ; check = check
    ; place = {!!} --ret' ∘ hash
    ; tt⟦_⟧m = Fv
    } where
      ret' : ∀ {a} → a → Mv a
      ret' a = λ vo → inj₂ (vo , a)
      bind' : ∀ {a b} → Mv a → (a → Mv b) → Mv b
      bind' ma f vo with ma vo
      ... | inj₂ (vo' , a) = f a vo'
      ... | inj₁ unit = inj₁ unit
      check : ∀ {τ} {wf : Wf● τ} → t⟦ τ ● wf ⟧V → tM⟦ τ ⟧V
      check dig [] = inj₁ unit
      check {τ} {wf} dig ((τ' , wf' , dat) ∷ vo) with τ' ≟T τ
      ... | no  _ = inj₁ unit
      ... | yes pf with hash {τ} {wf} (subst id (eq-shal pf) dat) ≟D dig
      ... | yes pf' = inj₂ (vo , subst id (VO-iso {τ} {wf}) (subst id (eq-shal pf) dat))
      ... | no _ = inj₁ unit

  ⟦_⟧V : ∀ {Γ τ} → Term Γ τ → Env {tM⟦_⟧V} Γ → tM⟦ τ ⟧V
  ⟦_⟧V = Denote.⟦_⟧m Verifier



  {- Correctness Relations -}

  mutual
    rel-correct : {τ : Ty} → t⟦ τ ⟧V → t⟦ τ ⟧I → t⟦ τ ⟧P → Set
    rel-correct {One} v i p = Unit
    rel-correct {τ₀ ⊗ τ₁} (v₀ , v₁) (i₀ , i₁) (p₀ , p₁) = rel-correct {τ₀} v₀ i₀ p₀ × rel-correct {τ₁} v₁ i₁ p₁
    rel-correct {τ₀ ⊕ τ₁} (inj₁ v) (inj₁ i) (inj₁ p) = rel-correct {τ₀} v i p
    rel-correct {τ₀ ⊕ τ₁} (inj₂ v) (inj₂ i) (inj₂ p) = rel-correct {τ₁} v i p
    rel-correct {τ₀ ⊕ τ₁} _ _ _ = ⊥
    rel-correct {τ₀ ⇒ τ₁} v i p = ∀ {v'} {i'} {p'} → m-rel-correct {τ₀} v' i' p' → m-rel-correct {τ₁} (v v') (i i') (p p')
    rel-correct {τ ● wf} v i p = {!!} --p ≡ merkleize {τ ● wf} {wf● wf} i × hash-s {τ ● wf} {wf● wf} (shallow {τ ● wf} {wf● wf} p) ≡ v

    m-rel-correct : {τ : Ty} → tM⟦ τ ⟧V → tM⟦ τ ⟧I → tM⟦ τ ⟧P → Set
    m-rel-correct {τ} v i (vo , p) = ∀ rest → rel' rest (v (vo ++ rest)) where
      rel' : List VO → Unit ⊎ List VO × t⟦ τ ⟧V → Set
      rel' _ (inj₁ Unit) = ⊥
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
  pf-correctP {_} {τ ● _} (auth x wf) ρ | v | i | p = ⟦ auth x wf ⟧V (projectV ρ) , ⟦ auth x wf ⟧I (projectI ρ) , ⟦ auth x wf ⟧P (projectP ρ) , {!!}
