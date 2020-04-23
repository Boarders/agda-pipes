module Pipes where

open import Categories.Functor
open import Categories.Category.Instance.Sets
open import Level
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality 


open ≡-Reasoning

postulate
  extensionality : ∀ {l l'} {S : Set l}{T : Set l'}
                   {f g : (x : S) -> T} ->
                   ((x : S) -> f x ≡ g x) ->
                   f ≡ g

_≡$_ : ∀ {l l'}{A : Set l} {B : A → Set l'} {f g : (x : A) → B x} →
       f ≡ g → (x : A) → f x ≡ g x
refl ≡$ x = refl

_$≡_ : ∀ {l l'}{A : Set l} {B : Set l'} {x y : A} →
       (f : A -> B) -> x ≡ y → f x ≡ f y
f $≡ refl = refl


_⟨≡_,_⟩  : ∀ {l l' l''}{A : Set l} {B : Set l'} {C : Set l''} {a a' : A}
       (f : A -> B -> C) -> a ≡ a' -> (b : B) → f a b ≡ f a' b
f ⟨≡ refl , b ⟩ = refl


data Proxy 
       (m : Set -> Set)
       (a' a b' b : Set)
       (r : Set)  : Set₁ where
  pure    : r -> Proxy m a' a b' b r
  effect  : ∀{x} -> m x ->  (x -> Proxy m a' a b' b r) -> Proxy m a' a b' b r
  request : a'       ->  (a -> Proxy m a' a b' b r) -> Proxy m a' a b' b r
  respond : b'       ->  (b -> Proxy m a' a b' b r) -> Proxy m a' a b' b r


1ℓ : Level
1ℓ = Level.suc 0ℓ

map-proxy 
  :  (m : Functor (Sets 0ℓ) (Sets 0ℓ))
  -> {a' a b' b : Set}
  -> {r r' : Set}
  -> (f : r -> r')
  -> Proxy (Functor.F₀ m) a' a b' b r -> Proxy (Functor.F₀ m) a' a b' b r'
map-proxy m f (pure r) = pure (f r)
map-proxy m f (effect mx cont[x])
  = effect mx (map-proxy m f ∘ cont[x])
map-proxy m f (request t[a'] cont[a])
  = request t[a'] ((map-proxy m f) ∘ cont[a])
map-proxy m f (respond t[b'] cont[b]) 
  = respond t[b'] ((map-proxy m f) ∘ cont[b])


id-law  
  :  (m : Functor (Sets 0ℓ) (Sets 0ℓ)) 
  -> {a' a b' b : Set}
  -> {r : Set}
  -> (p : Proxy (Functor.F₀ m) a' a b' b r)
  -> map-proxy m (λ r -> r) p ≡ p
id-law m (pure r) = refl
id-law m (effect mx cont[x])
  = begin 
      effect mx (\ x -> map-proxy m (\r -> r) (cont[x] x))
        ≡⟨ effect mx $≡ (extensionality (λ x -> id-law m (cont[x] x))) ⟩
      refl
id-law m (request t[a'] cont[a])
  = begin 
      request t[a'] (\ a -> map-proxy m (\r -> r) (cont[a] a))
        ≡⟨ request t[a'] $≡ (extensionality (λ a -> id-law m (cont[a] a))) ⟩
      refl
id-law m (respond t[b'] cont[b])
  = begin 
      respond t[b'] (\ b -> map-proxy m (\r -> r) (cont[b] b))
        ≡⟨ respond t[b'] $≡ (extensionality (λ b -> id-law m (cont[b] b))) ⟩
      refl


proxy-F : 
     (m : Functor (Sets 0ℓ) (Sets 0ℓ)) 
  -> (a' a b' b : Set)
  -> Functor (Sets 0ℓ) (Sets 1ℓ)
proxy-F m-func a' a b' b = 
  record
    { F₀ = Proxy m₀ a' a b' b
    ; F₁ = map-proxy m-func
    ; identity = id-law m-func _
    ; homomorphism = {!!}
    ; F-resp-≈ = {!!}
    }
  where
    open Functor m-func renaming (F₀ to m₀)


