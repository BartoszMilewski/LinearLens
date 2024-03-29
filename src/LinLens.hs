{-# language LinearTypes #-}
{-# language ScopedTypeVariables #-}
module LinLens where
import Prelude hiding ((.), id, Functor, fmap)

-- Existential Linear Lens
data LinLensEx a b s t where
  LinLensEx :: (s %1-> (c, a)) -> 
               ((c, b) %1-> t) -> LinLensEx a b s t

-- Linear lens
type LinLens s t a b = s %1-> (b %1-> t, a)

-- Proof of equivalence

fromLinLens :: forall s t a b.
  LinLens s t a b -> LinLensEx a b s t
fromLinLens h = LinLensEx f g
  where
    f :: s %1-> (b %1-> t, a)
    f = h
    g :: (b %1-> t, b) %1-> t
    g (set, b) = set b

toLinLens :: LinLensEx a b s t -> LinLens s t a b
toLinLens (LinLensEx f g) s = 
  case f s of
    (c, a) -> (\b -> g (c, b), a)

-- Linear profunctor
class Profunctor p where
  dimap :: (a' %1-> a) -> (b %1-> b') -> p a b -> p a' b'
  
-- Linear Tambara module
class (Profunctor p) => Tambara p where
   alpha :: forall a b c. p a b -> p (c, a) (c, b)

-- Linear lens is an instance of Tambara

instance Profunctor (LinLensEx a b) where
  dimap f' g' (LinLensEx f g) = LinLensEx (f . f') (g' . g)

instance Tambara (LinLensEx a b) where
  alpha (LinLensEx f g) = LinLensEx (unassoc . second f) (second g . assoc) 

idLens :: LinLensEx a b a b
idLens = LinLensEx unlunit lunit

-- Profunctor representation of a linear lens
type PLens a b s t = forall p. Tambara p => p a b -> p s t

-- Proof of equivalence
fromPLens :: PLens a b s t -> LinLensEx a b s t
fromPLens f = f idLens

toPLens :: LinLensEx a b s t -> PLens a b s t
toPLens (LinLensEx f g) pab = dimap f g (alpha pab)

-- Point free derivation

toLinLens2 :: LinLensEx a b s t -> LinLens s t a b
toLinLens2 (LinLensEx f g) = first ((g .) . eta) . f

-- van Laarhoven representation

type VLL s t a b = forall f. Functor f => 
    (a %1-> f b) -> (s %1-> f t)

toVLL :: LinLens s t a b -> VLL s t a b
toVLL lns f = fmap apply . strength . second f . lns

fromVLL :: forall s t a b. VLL s t a b -> LinLens s t a b
fromVLL vll s = unF (vll (F id) s)

data F a b x where
   F :: (b %1-> x) %1-> a %1-> F a b x

unF :: F a b x %1-> (b %1-> x, a)
unF (F bx a) = (bx, a)

instance Functor (F a b) where
  fmap f (F bx a) = F (f . bx) a

-- Monoidal category
-- Composition
(.) :: (b %1 -> c) %1 -> (a %1 -> b) %1 -> a %1 -> c
(f . g) x = f (g x)
-- Identity
id :: a %1-> a
id a = a

class Functor f where
  fmap :: (a %1-> b) %1-> f a %1-> f b

strength :: Functor f => (a, f b) %1-> f (a, b)
strength (a, fb) = fmap (eta a) fb


-- Functor CxC->C in a closed monoidal category
class Bifunctor p where
    bimap :: (a %1-> a') %1-> (b %1-> b') %1-> p a b %1-> p a' b'
    first :: (a %1-> a') %1-> p a b %1-> p a' b
    first f = bimap f id
    second :: (b %1-> b') %1-> p a b %1-> p a b'
    second = bimap id

-- The tensor product in a monoidal category is a bifunctor
instance Bifunctor (,) where
    bimap :: (a %1 -> a') %1-> (b %1 -> b') %1-> (a, b) %1-> (a', b')
    bimap f g (a, b) = (f a, g b)

-- The structure maps of a monoidal category
assoc :: ((a, b), c) %1-> (a, (b, c))
assoc ((a, b), c) = (a, (b, c))
unassoc :: (a, (b, c)) %1-> ((a, b), c)
unassoc (a, (b, c)) = ((a, b), c)

lunit :: ((), a) %1-> a
lunit ((), a) = a
unlunit :: a %1-> ((), a)
unlunit a = ((), a)

runit :: (a, ()) %1-> a
runit (a, ()) = a
unrunit :: a %1-> (a, ())
unrunit a = (a, ())

swap :: (a, b) %1-> (b, a)
swap (a, b) = (b, a)

-- Closed monoidal category 

curry :: ((a, b) %1-> c) %1-> (a %1-> (b %1-> c))
curry f x y = f (x, y)

uncurry :: (a %1-> (b %1-> c)) %1-> ((a, b) %1-> c)
uncurry f (x, y) = f x y 

-- unit of the currying adjunction
eta :: a %1-> b %1-> (a, b)
eta a b = (a, b)

-- counit of the currying adjunction
apply :: (a %1-> b, a) %1-> b
apply (f, a) = f a

newtype Hom a b = Hom (a %1-> b)

instance Profunctor Hom where
  dimap f g (Hom h) = Hom (g . h . f)

main :: IO ()
main = return ()