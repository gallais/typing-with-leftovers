module linear.Usage where

open import Data.Unit
open import Data.Bool
open import Data.Nat as ℕ
open import Data.Fin
open import Data.Product
open import Function
open import linear.Relation.Functional

open import linear.Type
open import linear.Scope as Sc
  hiding (Mergey ; copys ; inserts
        ; Extending
        ; Weakening ; weakFin
        ; Env ; Substituting
        ; Freshey ; withFreshVars)
open import linear.Context as C
  hiding (Mergey ; _⋈_ ; copys ; inserts
         ; _++_ ; ++copys-elim)
open import Relation.Binary.PropositionalEquality


-- Usage: fresh or stale
infix 6 `fresh_ `stale_ fresh_ stale_
data Usage : (a : Type) → Set where
  `fresh_ : (a : Type) → Usage a
  `stale_ : (a : Type) → Usage a

`Usage! : Type! → Set
`Usage! (σ !^ false) = Usage σ
`Usage! _            = ⊤

-- wrapper to facilitate type inference
record Usage! (σ : Type!) : Set where
  constructor [_]
  field usage! : `Usage! σ
open Usage! public

fresh_ : (σ : Type!) → Usage! σ
fresh σ !^ false = [ `fresh σ ]
fresh σ !^ true  = [ tt       ]

stale_ : (σ : Type!) → Usage! σ
stale σ !^ false = [ `stale σ ]
stale σ !^ true  = [ tt       ]

infixr 5 _∷_ □_
data Usages : {n : ℕ} (γ : Context n) → Set where
  []  : Usages []
  _∷_ : {n : ℕ} {γ : Context n} {a : Type!} →
        Usage! a → Usages γ →
        Usages (a ∷ γ)
  □_  : {n : ℕ} {γ : Context n} →
        Usages γ → Usages (□ γ)

unbox : {n : ℕ} {γ : Context n} → Usages (□ γ) → Usages γ
unbox (□ Γ) = Γ

head : {n : ℕ} {γ : Context n} {a : Type!} → Usages (a ∷ γ) → Usage! a
head (S ∷ _) = S

tail : {n : ℕ} {γ : Context n} {a : Type!} → Usages (a ∷ γ) → Usages γ
tail (_ ∷ Γ) = Γ

infixr 4 _++_
_++_ : {m n : ℕ} {γ : Context m} {δ : Context n}
       (Γ : Usages γ) (Δ : Usages δ) → Usages (γ C.++ δ)
[]    ++ Δ = Δ
S ∷ Γ ++ Δ = S ∷ (Γ ++ Δ)
□ Γ   ++ Δ = □ (Γ ++ Δ)

-- De Bruijn index as resource consumption
infix 1 _⊢var_∈_⊠_
infixr 5 op_ wk_
data _⊢var_∈_⊠_ :
  {n : ℕ} {γ : Context n}
  (Γ : Usages γ) (k : Fin n) (σ : Type!) (Δ : Usages γ) → Set where

  -- axiom: linear resources can only be used once. They are turned
  -- from fresh to stale when consumed (nb: as fresh = stale for
  -- resources of type σ!, it doesn't prevent us from using them
  -- multiple times!)
  z   : {n : ℕ} {γ : Context n} {Γ : Usages γ} {σ : Type!} →
        -----------------------------------------------------------
        fresh σ ∷ Γ ⊢var zero ∈ σ ⊠ stale σ ∷ Γ

  -- weak: one can ignore a resource. In the output context it is
  -- simply left unchanged
  wk_ : {n : ℕ} {γ : Context n} {k : Fin n} {Γ Δ : Usages γ}
        {σ τ : Type!} {S : Usage! τ} →
            Γ ⊢var k ∈ σ ⊠ Δ →
        ----------------------------
        S ∷ Γ ⊢var suc k ∈ σ ⊠ S ∷ Δ

  -- finally, when escaping a box (i.e. during the proof of a
  -- type (σ !)), the looked up resource has to be non-linear
  -- (otherwise when duplicating the body, one would not be able
  -- to duplicate the variable)
  op_ : {n : ℕ} {γ : Context n} {k : Fin n} {Γ Δ : Usages γ} {σ : Type!} →
        Γ ⊢var k ∈ σ ! ⊠ Δ →
        ----------------------
        □ Γ ⊢var k ∈ σ ⊠ □ Δ

f⌜_⌝ : {n : ℕ} (γ : Context n) → Usages γ
f⌜ []     ⌝ = []
f⌜ σ ∷ γ ⌝ = fresh σ ∷ f⌜ γ ⌝
f⌜ □ γ   ⌝ = □ f⌜ γ ⌝

s⌜_⌝ : {n : ℕ} (γ : Context n) → Usages γ
s⌜ []     ⌝ = []
s⌜ σ ∷ γ ⌝ = stale σ ∷ s⌜ γ ⌝
s⌜ □ γ   ⌝ = □ s⌜ γ ⌝

data Mergey : {k l : ℕ} {m : Sc.Mergey k l} (M : C.Mergey m) → Set where
  finish : {k : ℕ} → Mergey (finish {k})
  copy   : {k l : ℕ} {m : Sc.Mergey k l} {M : C.Mergey m} →
           Mergey M → Mergey (copy M)
  insert : {k l : ℕ} {m : Sc.Mergey k l} {M : C.Mergey m} {a : Type!} →
           Usage! a → Mergey M → Mergey (insert a M)

copys : (o : ℕ) {k l : ℕ} {m : Sc.Mergey k l} {M : C.Mergey m} →
        Mergey M → Mergey (C.copys o M)
copys zero    M = M
copys (suc o) M = copy (copys o M)

inserts : {o k l : ℕ} {O : Context o} (𝓞 : Usages O)
          {m : Sc.Mergey k l} {M : C.Mergey m} →
          Mergey M → Mergey (C.inserts O M)
inserts []      𝓜 = 𝓜
inserts (S ∷ 𝓞) 𝓜 = insert S (inserts 𝓞 𝓜)
inserts (□ 𝓞)   𝓜 = inserts 𝓞 𝓜

infixl 3 _⋈_
_⋈_ : {k l : ℕ} {γ : Context k} {m : Sc.Mergey k l} {M : C.Mergey m}
      (Γ : Usages γ) (𝓜 : Mergey M) → Usages (γ C.⋈ M)
Γ     ⋈ finish       = Γ
S ∷ Γ ⋈ copy 𝓜     = S ∷ (Γ ⋈ 𝓜)
-- need to eta-expand these clauses by distinguishing
-- each 𝓜 case to get the return type to reduce properly
□ Γ   ⋈ copy 𝓜     = □ (Γ ⋈ copy 𝓜)
□ Γ   ⋈ insert S 𝓜 = □ (Γ ⋈ insert S 𝓜)
-- same here with Γ
[]    ⋈ insert S 𝓜 = S ∷ ([] ⋈ 𝓜)
T ∷ Γ ⋈ insert S 𝓜 = S ∷ (T ∷ Γ ⋈ 𝓜)

⋈ˡ : (ri : Σ[ klγ ∈ Σ[ k ∈ ℕ ] ℕ × Context k ]
           Σ[ mM ∈ (Σ[ m ∈ Sc.Mergey (proj₁ klγ) (proj₁ (proj₂ klγ)) ]
                    C.Mergey m) ]
             Mergey (proj₂ mM) × Usages (proj₂ (proj₂ klγ) C.⋈ proj₂ mM))
     (ii : ⊤) (o : let ((_ , _ , γ) , _) = ri in Usages γ) → Set
⋈ˡ (_ , _ , 𝓜 , Γ) ii Γ′ = Γ ≡ (Γ′ ⋈ 𝓜)

⋈ˡ-injective : Functional ⋈ˡ
⋈ˡ-injective (_ , _ , finish   , Γ) eq₁ eq₂ = trans (sym eq₁) eq₂
⋈ˡ-injective (_ , _ , copy 𝓜 , S ∷ Γ) {o₁ = σ ∷ o₁} {τ ∷ o₂} eq₁ eq₂ =
  cong₂ _∷_ (cong head $ trans (sym eq₁) eq₂)
  $ ⋈ˡ-injective (_ , _ , 𝓜 , Γ) (cong tail eq₁) (cong tail eq₂)
⋈ˡ-injective (_ , _ , copy 𝓜 , □ Γ) {o₁ = □ o₁} {□ o₂} eq₁ eq₂ =
  cong □_
  $ ⋈ˡ-injective (_ , _ , copy 𝓜 , Γ) (cong unbox eq₁) (cong unbox eq₂)
⋈ˡ-injective (_ , _ , insert S 𝓜 , □ Γ) {o₁ = □ o₁} {□ o₂} eq₁ eq₂ =
  cong □_
  $ ⋈ˡ-injective (_ , _ , insert S 𝓜 , Γ) (cong unbox eq₁) (cong unbox eq₂)
⋈ˡ-injective (_ , _ , insert S 𝓜 , Γ) {o₁ = []} {[]} eq₁ eq₂ = refl
⋈ˡ-injective (_ , _ , insert S 𝓜 , T ∷ Γ) {o₁ = σ ∷ o₁} {τ ∷ o₂} eq₁ eq₂ =
  ⋈ˡ-injective (_ , _ , 𝓜 , Γ) {o₁ = σ ∷ o₁} {τ ∷ o₂}
  (cong tail eq₁) (cong tail eq₂)


++copys-elim₂ :
  {k l o : ℕ} {m : Sc.Mergey k l} {M : C.Mergey m}
  {δ : Context o} {γ : Context k}
  (P : {γ : Context (o ℕ.+ l)} → Usages γ → Usages γ → Set)
  (Δ Δ′ : Usages δ) (Γ Γ′ : Usages γ) (𝓜 : Mergey M) →
  P ((Δ ++ Γ) ⋈ copys o 𝓜) ((Δ′ ++ Γ′) ⋈ copys o 𝓜) →
  P (Δ ++ (Γ ⋈ 𝓜)) (Δ′ ++ (Γ′ ⋈ 𝓜))
++copys-elim₂ P []      []       Γ Γ′ 𝓜 p = p
++copys-elim₂ P (S ∷ Δ) (T ∷ Δ′) Γ Γ′ 𝓜 p =
  ++copys-elim₂ (λ Θ Θ′ → P (S ∷ Θ) (T ∷ Θ′)) Δ Δ′ Γ Γ′ 𝓜 p
++copys-elim₂ {o = suc _} P (□ Δ)   (□ Δ′)   Γ Γ′ 𝓜 p =
  ++copys-elim₂ (λ Θ Θ′ → P (□ Θ) (□ Θ′)) Δ Δ′ Γ Γ′ 𝓜 p
++copys-elim₂ {o = zero} P (□ Δ) (□ Δ′) Γ Γ′ finish         p = p
++copys-elim₂ {o = zero} P (□ Δ) (□ Δ′) Γ Γ′ (copy 𝓜)     p =
  ++copys-elim₂ (λ Θ Θ′ → P (□ Θ) (□ Θ′)) Δ Δ′ Γ Γ′ (copy 𝓜) p
++copys-elim₂ {o = zero} P (□ Δ) (□ Δ′) Γ Γ′ (insert S 𝓜) p =
  ++copys-elim₂ (λ Θ Θ′ → P (□ Θ) (□ Θ′)) Δ Δ′ Γ Γ′ (insert S 𝓜) p

-- We can give an abstract interface to describe these relations
-- by introducing the notion of `Typing`. It exists for `Fin`,
-- `Check` and `Infer`:
Typing : (T : ℕ → Set) → Set₁
Typing T = {n : ℕ} {γ : Context n}
           (Γ : Usages γ) (t : T n) (σ : Type!) (Δ : Usages γ) → Set

-- The notion of 'Usage Weakening' can be expressed for a `Typing`
-- of `T` if it enjoys `Scope Weakening`
Weakening : (T : ℕ → Set) (Wk : Sc.Weakening T) (𝓣 : Typing T) → Set
Weakening T Wk 𝓣 =
  {k l : ℕ} {γ : Context k} {Γ Δ : Usages γ}
  {m : Sc.Mergey k l} {M : C.Mergey m} (𝓜 : Mergey M)
  {σ : Type!} {t : T k} →
  𝓣 Γ t σ Δ → 𝓣 (Γ ⋈ 𝓜) (Wk m t) σ (Δ ⋈ 𝓜)
  
-- A first example of a Typing enjoying Usage Weakening: Fin.
TFin : Typing Fin
TFin = _⊢var_∈_⊠_

weakFin : Weakening Fin Sc.weakFin TFin
weakFin finish         k      = k
weakFin (copy 𝓜)     z      = z
weakFin (copy 𝓜)     (wk k) = wk weakFin 𝓜 k
weakFin (copy 𝓜)     (op k) = op weakFin (copy 𝓜) k
-- same as before: we need to eta-expand by case-splitting on
-- Γ and Δ to get the goal type to reduce
weakFin {Γ = []}    {[]}    (insert S 𝓜) k      = wk weakFin 𝓜 k
weakFin {Γ = T ∷ Γ} {U ∷ Δ} (insert S 𝓜) k      = wk weakFin 𝓜 k
weakFin {Γ = □ Γ}   {□ Δ}   (insert S 𝓜) (op k) = op weakFin (insert S 𝓜) k

-- Similarly to 'Usage Weakening', the notion of 'Usage Substituting'
-- can be expressed for a `Typing` of `T` if it enjoys `Scope Substituting`

data Env {E : ℕ → Set} (𝓔 : Typing E) : {k l : ℕ}
  {θ : Context l}    -- the context the definitions in the env live in
  (T₁ : Usages θ)    -- the input usage of the environment
  (ρ : Sc.Env E k l) -- the raw substitution it corresponds to
  (Τ₂ : Usages θ)    -- the output usage of the environment
  {γ : Context k}
  (Γ : Usages γ)     -- the target the environment covers
   → Set where

  []    : {l : ℕ} {θ : Context l} {Τ₁ : Usages θ} →
          ------------------
          Env 𝓔 Τ₁ [] Τ₁ []

  _∷_   : {a : Type!} {k l : ℕ} {θ : Context l} {ρ : Sc.Env E k l} {t : E l}
          {Τ₁ Τ₂ Τ₃ : Usages θ} {γ : Context k} {Γ : Usages γ} →
          𝓔 Τ₁ t a Τ₂ → Env 𝓔 Τ₂ ρ Τ₃ Γ →
          ---------------------------------
          Env 𝓔 Τ₁ (t ∷ ρ) Τ₃ (fresh a ∷ Γ)

  ─∷_   : {a : Type} {k l : ℕ}  {θ : Context l} {ρ : Sc.Env E k l} {t : E l}
          {Τ₁ Τ₂ : Usages θ} {γ : Context k} {Γ : Usages γ} →
          Env 𝓔 Τ₁ ρ Τ₂ Γ →
          -----------------------------------
          Env 𝓔 Τ₁ (t ∷ ρ) Τ₂ (stale (a !^ false) ∷ Γ)

  [v]∷_ : {a : Type!} {k l : ℕ} {θ : Context l} {ρ : Sc.Env E k l}
          {Τ₁ Τ₂ : Usages θ} {γ : Context k} {Γ : Usages γ} →
          Env 𝓔 Τ₁ ρ Τ₂ Γ →
          -----------------------------------------------------------
          Env 𝓔 (fresh a ∷ Τ₁) (v∷ ρ) (fresh a ∷ Τ₂) (fresh a ∷ Γ)

  ]v[∷_ : {a : Type} {k l : ℕ} {θ : Context l} {ρ : Sc.Env E k l}
          {Τ₁ Τ₂ : Usages θ} {γ : Context k} {Γ : Usages γ} →
          Env 𝓔 Τ₁ ρ Τ₂ Γ →
          -----------------------------------------------------------
          Env 𝓔 (stale (a !^ false) ∷ Τ₁) (v∷ ρ) (stale (a !^ false) ∷ Τ₂) (stale (a !^ false) ∷ Γ)

  □_    : {k l : ℕ} {θ : Context l} {ρ : Sc.Env E k l}
          {Τ₁ Τ₂ : Usages θ} {γ : Context k} {Γ : Usages γ} →
          Env 𝓔 Τ₁ ρ Τ₂ Γ →
          ---------------------
          Env 𝓔 (□ Τ₁) ρ (□ Τ₂) (□ Γ)


-- A term does not necessarily use up all of the resources
-- available in the context. As such the result of a substitution
-- algorithm has to be both a term into which the substitution has
-- been performed *but also* a leftover environment.

Substituting :
   (E T : ℕ → Set)               -- A type of raw environment values and terms
   ([_]_ : Sc.Substituting E T)  -- The proof the environment can be substituted
                                 -- into the terms
   (𝓔 : Typing E)               -- Typing relation for the environment values
   (𝓣 : Typing T)               -- Typing relation for the terms
    → Set
Substituting E T subst 𝓔 𝓣 =
  {k l : ℕ} {θ : Context l} {ρ : Sc.Env E k l}
  {Τ₁ Τ₂ : Usages θ} {γ : Context k}
  {Γ Δ : Usages γ} {σ : Type!} {t : T k} →
  Env 𝓔 Τ₁ ρ Τ₂ Γ → 𝓣 Γ t σ Δ →
  ---------------------------------------------------
  ∃ λ Τ₃ → 𝓣 Τ₁ (subst ρ t) σ Τ₃ × Env 𝓔 Τ₃ ρ Τ₂ Δ

f^Extending :
  (E : ℕ → ℕ → Set) (Ext : Sc.Extending E)
  (𝓔 : {k l : ℕ} {θ : Context l} (T₁ : Usages θ) (ρ : E k l) (Τ₂ : Usages θ)
        {γ : Context k} (Γ : Usages γ) → Set)
  → Set
f^Extending E Ext 𝓔 =
  {k l o : ℕ} {θ : Context l} {Τ₁ Τ₂ : Usages θ}
  {e : E k l} {γ : Context k} {Γ : Usages γ}
  (δ : Context o) → 𝓔 Τ₁ e Τ₂ Γ →
  -----------------------------------------------------------
  𝓔 (f⌜ δ ⌝ ++ Τ₁) (Ext o e) (f⌜ δ ⌝ ++ Τ₂) (f⌜ δ ⌝ ++ Γ)

s^Extending :
  (E : ℕ → ℕ → Set) (Ext : Sc.Extending E)
  (𝓔 : {k l : ℕ} {θ : Context l} (T₁ : Usages θ) (ρ : E k l) (Τ₂ : Usages θ)
        {γ : Context k} (Γ : Usages γ) → Set)
  → Set
s^Extending E Ext 𝓔 =
  {k l o : ℕ} {θ : Context l} {Τ₁ Τ₂ : Usages θ}
  {e : E k l} {γ : Context k} {Γ : Usages γ}
  (δ : Context o) → 𝓔 Τ₁ e Τ₂ Γ →
  -----------------------------------------------------------
  𝓔 (s⌜ δ ⌝ ++ Τ₁) (Ext o e) (s⌜ δ ⌝ ++ Τ₂) (s⌜ δ ⌝ ++ Γ)

record Freshey (E : ℕ → Set) (F : Sc.Freshey E) (𝓔 : Typing E) : Set where
  field
    fresh : {k : ℕ} {γ : Context k} {Γ : Usages γ} (σ : Type!) →
            𝓔 (fresh σ ∷ Γ) (Sc.Freshey.fresh F {k}) σ (stale σ ∷ Γ)
    weak  : Weakening E (Sc.Freshey.weak F) 𝓔

withFreshVars : {E : ℕ → Set} {𝓔 : Typing E} →
                f^Extending (Sc.Env E) Sc.withFreshVars (Env 𝓔)
withFreshVars []      ρ = ρ
withFreshVars (a ∷ δ) ρ = [v]∷ withFreshVars δ ρ
withFreshVars (□ δ)   ρ = □ withFreshVars δ ρ

withStaleVars : {E : ℕ → Set} {𝓔 : Typing E} →
                s^Extending (Sc.Env E) Sc.withFreshVars (Env 𝓔)
withStaleVars []                ρ = ρ
withStaleVars (a !^ false ∷ δ)  ρ = ]v[∷ withStaleVars δ ρ
withStaleVars (a !^ true  ∷ δ)  ρ = [v]∷ withStaleVars δ ρ
withStaleVars (□ δ)             ρ = □ withStaleVars δ ρ
