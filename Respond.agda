module Respond where


open import Categories.Functor
open import Categories.Category.Instance.Sets
open import Level
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
open import Categories.Category

open ≡-Reasoning
open import Pipes
open import Data.Product using (_×_; proj₁; proj₂)


send
  :  {m : Functor (Sets 0ℓ) (Sets 0ℓ)}
  -> {a' a b' b : Set}
  -> {x x' : Set}
  -> a
  -> Proxy (Functor.F₀ m) x' x a' a a'
send a = respond a pure

{-
                              /===> b
                             /      |
     +---------+            /  +----|----+            +---------+
     |         |           /   |    v    |            |         |
 x' <==       <== b' <==\ / x'<==       <== c'    x' <==       <== c'
     |    f    |         X     |    g    |     =      | f //> g |
 x  ==>       ==> b  ===/ \ x ==>       ==> c     x  ==>       ==> c'
     |    |    |           \   |    |    |            |    |    |
     +----|----+            \  +----|----+            +----|----+
          v                  \      v                      v
          a'                  \==== b'                     a'

-}

respond-$
  :  (m : Functor (Sets 0ℓ) (Sets 0ℓ))
  -> {a' b b' c c' x x' : Set}
  -> Proxy (Functor.F₀ m) x' x b' b a'
  -> (b -> Proxy (Functor.F₀ m) x' x c' c b')
  -> Proxy (Functor.F₀ m) x' x  c' c a'
respond-$ m (pure a) fb = pure a
respond-$ m (effect  me cont[e]) fb 
  = effect me (\ e -> (respond-$ m  (cont[e] e) fb))
respond-$ m (request x' cont[x']) fb 
  = request x' (\ x' -> (respond-$ m (cont[x'] x') fb))
respond-$ m (respond  b  cont[b']) fb 
  = bind-proxy {m} (fb b) (\ b' -> respond-$ m (cont[b'] b') fb)


_∙_/>/_
  :  {a a' b b' c c' : Set}
  -> {x x' : Set}
  -> (m : Functor (Sets 0ℓ) (Sets 0ℓ))
  -> (a -> Proxy (Functor.F₀ m) x' x b' b a')
  -> (b -> Proxy (Functor.F₀ m) x' x c' c b')
  -> (a -> Proxy (Functor.F₀ m) x' x c' c a')
_∙_/>/_ m fa fb a  = respond-$ m (fa a)  fb

_∙_/</_
  :  {a a' b b' c c' : Set}
  -> {x x' : Set}
  -> (m : Functor (Sets 0ℓ) (Sets 0ℓ))
  -> (b -> Proxy (Functor.F₀ m) x' x c' c b')
  -> (a -> Proxy (Functor.F₀ m) x' x b' b a')
  -> (a -> Proxy (Functor.F₀ m) x' x c' c a')
_∙_/</_ m fb fa a  = respond-$ m (fa a)  fb

{-# NON_TERMINATING #-}
respond-assoc-law
   :  {A B C D : Set × Set}
   -> {x x' : Set}
   -> (m : Functor (Sets 0ℓ) (Sets 0ℓ))
   -> (f : proj₁ A → Proxy (Functor.F₀ m) x' x (proj₂ B) (proj₁ B) (proj₂ A))
   -> (g : proj₁ B → Proxy (Functor.F₀ m) x' x (proj₂ C) (proj₁ C) (proj₂ B))
   -> (h : proj₁ C → Proxy (Functor.F₀ m) x' x (proj₂ D) (proj₁ D) (proj₂ C))
   -> {a₁ : proj₁ A} →
      respond-$ m (f a₁) (λ a → respond-$ m (g a) h) ≡
      respond-$ m (respond-$ m (f a₁) g) h
respond-assoc-law m f g h {a₁}
        with (f a₁)
respond-assoc-law m f g h {a₁} | pure a₂ = refl
respond-assoc-law m f g h {a₁} | effect me cont[me] 
 = begin 
     effect me (\ e -> respond-$ m (cont[me] e) (\ a -> respond-$ m (g a) h))
    ≡⟨ effect me $≡
        (extensionality
          (\ e -> respond-assoc-law m cont[me] g h )) ⟩
      (effect me (λ e → respond-$ m (respond-$ m (cont[me] e) g) h))
    ∎
respond-assoc-law m f g h {a₁} | request x' cont[x]
 = begin 
     request x' (\ x -> respond-$ m (cont[x] x) (\ a -> respond-$ m (g a) h))
    ≡⟨ request x' $≡
        (extensionality
          (\ x -> respond-assoc-law m cont[x] g h )) ⟩
       request x' (λ x → respond-$ m (respond-$ m (cont[x] x) g) h)
    ∎
respond-assoc-law m f g h {a₁} | respond b₁ cont[b₂] = {!!}
{-
 = begin 
     bind-proxy (respond-$ m (g b₁) h)
      (λ b' → respond-$ m (cont[b₂] b') (λ a → respond-$ m (g a) h))
     respond b₁ (\ b₂ -> respond-$ m (cont[b₂] b₂) (\ a -> respond-$ m (g a) h))
    ≡⟨ respond b₁ $≡ 
        (extensionality 
          (\ x -> respond-assoc-law m cont[b₂] g h )) ⟩
       respond b₁ (λ b₂ → respond-$ m (respond-$ m (cont[b₂] b₂) g) h)
    ∎
-}

respond-cat
  : {x' x : Set} 
  -> (m : Functor (Sets 0ℓ) (Sets 0ℓ))
  -> Category 1ℓ 1ℓ 1ℓ
respond-cat {x'} {x} m =
  record
    { Obj = Set × Set
    ; _⇒_ 
        = λ a×a' b×b' -> proj₁ a×a' -> Proxy m₀ x' x (proj₂ b×b') (proj₁ b×b') (proj₂ a×a')
    ; _≈_ = λ f g -> ∀ {x} -> f x ≡ g x
    ; id = \ {a×a'} -> send {m} {_} {_} {_} {_} {_} {_}
    ; _∘_ = m ∙_/</_
    ; assoc = respond-assoc-law m _ _ _
    ; sym-assoc = {!!}
    ; identityˡ = {!!}
    ; identityʳ = {!!}
    ; identity² = {!!}
    ; equiv = {!!}
    ; ∘-resp-≈ = {!!}
    }
  where
    open Functor m renaming (F₀ to m₀)

