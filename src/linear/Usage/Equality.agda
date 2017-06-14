module linear.Usage.Equality where

open import Data.Nat
open import Data.Product
open import Function
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import linear.Type hiding (eq ; eq!)
open import linear.Context
open import linear.Usage
open import linear.RawIso

eq : {a : Type} (A B : Usage a) → Dec (A ≡ B)
eq (`fresh a) (`fresh .a) = yes refl
eq (`fresh a) (`stale .a) = no (λ ())
eq (`stale a) (`fresh .a) = no (λ ())
eq (`stale a) (`stale .a) = yes refl

RawIso-[] : {a : Type} {A B : Usage a} →
            RawIso (A ≡ B) ((Usage! (a !^ 0) ∋ [ A ]) ≡ ([ B ]))
push RawIso-[] refl = refl
pull RawIso-[] refl = refl


eq! : {a : Type!} (A B : Usage! a) → Dec (A ≡ B)
eq! {a !^ zero}  [ A ] [ B ] = RawIso-[] <$> eq A B
eq! {a !^ suc p} [ A ] [ B ] = yes refl

RawIso-∷ : {n : ℕ} {γ : Context n} {Γ Δ : Usages γ} {a : Type!} {A B : Usage! a} →
           RawIso (A ≡ B × Γ ≡ Δ) ((Usages (a ∷ γ) ∋ A ∷ Γ) ≡ (B ∷ Δ))
push RawIso-∷ (refl , refl) = refl
pull RawIso-∷ refl          = refl , refl


RawIso-□ : {n : ℕ} {γ : Context n} {Γ Δ : Usages γ}  →
           RawIso (Γ ≡ Δ) ((Usages (□ γ) ∋ □ Γ) ≡ (□ Δ))
push RawIso-□ refl = refl
pull RawIso-□ refl = refl

eqs : {n : ℕ} {γ : Context n} (Γ Δ : Usages γ) → Dec (Γ ≡ Δ)
eqs []      []      = yes refl
eqs (A ∷ Γ) (B ∷ Δ) = RawIso-∷ <$> eq! A B <*> eqs Γ Δ
eqs (□ Γ)   (□ Δ)   = RawIso-□ <$> eqs Γ Δ
