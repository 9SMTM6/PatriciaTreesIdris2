import Data.Vect
import Decidable.Equality

data PrefixTree : (len : Nat) -> (tVal : Type) -> Type where
    Leaf : (val : tVal) -> PrefixTree 0 tVal
    Left : (left : PrefixTree len tVal) -> PrefixTree (S len) tVal
    Right : (right : PrefixTree len tVal) -> PrefixTree (S len) tVal
    Both : (left : PrefixTree len tVal) -> (right : PrefixTree len tVal) -> PrefixTree (S len) tVal

Key : (len: Nat) -> Type
Key len = Vect len Bool

-- todo: enter errors once tests are established

-- IDK if I did this syntax properly
-- {0 len: Nat} ->
total
singleton : (key: Key len) -> (val: tVal) -> PrefixTree len tVal
singleton [] val = Leaf val
singleton (x :: xs) val = do
    let remainder = singleton xs val
    case x of
        False => Left remainder
        True => Right remainder

total
insert : Key len -> tVal -> PrefixTree len tVal -> PrefixTree len tVal
-- termination
insert [] val trie = Leaf val
-- termination: with singleton
insert (False::xs) val (Right rTrie) = Both (singleton xs val) rTrie
insert (True::xs) val (Left lTrie) = Both lTrie (singleton xs val)
-- recursion: sparse
insert (False::xs) val (Left lTrie) = Left (insert xs val lTrie)
insert (True::xs) val (Right rTrie) = Right (insert xs val rTrie)
-- recursion: dense
insert (False::xs) val (Both lTrie rTrie) = Both (insert xs val lTrie) rTrie
insert (True::xs) val (Both lTrie rTrie) = Both lTrie (insert xs val rTrie)
-- "not impossible" ?!
-- does it not recognize that leaf variant with non empty list is not a possibility?
-- cause it should...
-- and why does it not list the reason its possible?
-- insert xs val trie impossible

total
lookup : Key len -> PrefixTree len tVal -> Maybe tVal
-- termination
lookup [] (Leaf val) = Just val
lookup (False::xs) (Right _) = Nothing
lookup (True::xs) (Left _) = Nothing
-- recursion: sparse
lookup (False::xs) (Left lTrie) = lookup xs lTrie
lookup (True::xs) (Right rTrie) = lookup xs rTrie
-- recursion: dense
lookup (x::xs) (Both lTrie rTrie) = Main.lookup xs (case x of
        False => lTrie
        True => rTrie
    )
-- lookup key trie impossible

total
||| "last" element (so the elements from the 2nd prefix tree) will win
||| so its value will be in the resulting set
-- todo: type-testcase for that
union : PrefixTree len tVal -> PrefixTree len tVal -> PrefixTree len tVal
-- termination
union (Leaf _) (Leaf val1) = Leaf val1
union (Left lTrie) (Right rTrie) = Both lTrie rTrie
union (Right rTrie) (Left lTrie) = Both lTrie rTrie
-- recursion: same
union (Left lTrie0) (Left lTrie1) = Left (union lTrie0 lTrie1)
union (Right rTrie0) (Right rTrie1) = Right (union rTrie0 rTrie1)
union (Both lTrie0 rTrie0) (Both lTrie1 rTrie1) = Both (union lTrie0 lTrie1) (union rTrie0 rTrie1)
-- recursion: different (one must be Both, otherwise termination)
union (Left lTrie0) (Both lTrie1 rTrie1) = Both (union lTrie0 lTrie1) rTrie1
union (Right rTrie0) (Both lTrie1 rTrie1) = Both lTrie1 (union rTrie0 rTrie1)
union (Both lTrie0 rTrie0) (Left lTrie1) = Both (union lTrie0 lTrie1) rTrie0
union (Both lTrie0 rTrie0) (Right rTrie1) = Both lTrie0 (union rTrie0 rTrie1)

total
delete: Key len -> PrefixTree len tVal -> Maybe (PrefixTree len tVal)
delete [] (Leaf _) = Nothing
delete (False::xs) remains@(Right _) = Just remains
delete (True::xs) remains@(Left _) = Just remains
delete (False::xs) (Left trie) = map Left (delete xs trie)
delete (True::xs) (Right trie) = map Right (delete xs trie)
delete (False::xs) (Both lTrie rTrie) = do
    let lDeleted = delete xs lTrie
    Just (
        case lDeleted of
            Nothing => Right rTrie
            Just lDelInner => Both lDelInner rTrie
        )
delete (True::xs) (Both lTrie rTrie) = do
    let rDeleted = delete xs rTrie
    Just (
        case rDeleted of
            Nothing => Left lTrie
            Just rDelInner => Both lTrie rDelInner
        )

total
-- todo: OUTDATED
-- explanation return type: an intersection might be smaller, importantly it might be entirely empty.
-- we could introduce an empty tree marker,
-- but that would mean that the tree can end up in a messy state with empty trees
-- at the ends of long prefixes.
-- Thats hugely inefficient and makes things more messy to implement.
-- Thus we want to delete parts going nowhere.
-- But in that case the resulting tree might be smaller in depth (len).
-- thus we need to be able to go smaller.
-- But idris2 doesnt like len coming out of nowhere, understandibly.
-- With dependent pairs the len will be an explicit part of the return type,
-- in ways that both the code and type system can read its value, which idris likes.
-- The parts with Fin just record that the resulting tree may be smaller, not larger in key len.
||| "last" element (so the elements from the 2nd prefix tree) will win
||| so its value will be in the resulting set
intersection : PrefixTree len tVal -> PrefixTree len tVal -> Maybe (PrefixTree len tVal)
intersection (Right _) (Left val1) = Nothing
intersection (Left _) (Right val1) = Nothing
intersection (Leaf _) winner@(Leaf val1) = Just winner
intersection (Both lTrie0 _) (Left lTrie1) = map Left (intersection lTrie0 lTrie1)
intersection (Both _ rTrie0) (Right rTrie1) = map Right (intersection rTrie0 rTrie1)
intersection (Left lTrie0) (Both lTrie1 _) = map Left (intersection lTrie0 lTrie1)
intersection (Right rTrie0) (Both _ rTrie1) = map Right (intersection rTrie0 rTrie1)
intersection (Right rTrie0) (Right rTrie1) = map Right (intersection rTrie0 rTrie1)
intersection (Left lTrie0) (Left lTrie1) = map Left (intersection lTrie0 lTrie1)
intersection (Both lTrie0 rTrie0) (Both lTrie1 rTrie1) = do
    lInt <- (intersection lTrie0 lTrie1)
    rInt <- (intersection rTrie0 rTrie1)
    Just (Both lInt rInt)

total
thm_emptyingTrie : (key: Key len) -> (val: tVal) -> delete key (singleton key val) = Nothing
thm_emptyingTrie key val = do
    ?current

total
thm_lookupInserted : (key: Key len) -> (val: tVal) -> (trie: PrefixTree len tVal) -> lookup key (insert key val trie) = Just val
thm_lookupInserted key val trie = do
    let laa = decEq 3 (1+2)
    ?future

ex = singleton ([False, True, False]) "hello world"

ex1 = insert ([False, True, True]) "inserted" ex

val: (n : Nat ** Vect n Nat)
val = (3 ** [4,3,5])

ex2 = Both (Both (Left (Leaf 2)) (Right (Leaf 3))) (Left (Right (Leaf 3)))

-- todo theoreme

-- main : IO ()
-- main = do
--     let ex = singleton ([False, True, False]) "hello world"
--     printLn ex
--     pure ()