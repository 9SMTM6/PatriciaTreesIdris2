-- suggestion for v1 from Philipp (with renaming, type alias etc)
-- inferiert: zunächst manuelles bauen, ist binärbaum/ hat radix 2 = 2^1 (wg 'Vect len Bool')
-- sofortige impl als Map, pure Set impl nicht so wichtig.
-- v1 doesnt support the thing that makes patrica trees patricia trees:
  -- that they can hold more than one byte per edge
  -- well, it retains the property that the key is spread over the structure, but its actually just a binary prefix tree
-- v2 adds the ability to hold more bytes per edge / is an optimization
-- v3 uses a packed key repr instead of (probably) sparse Vect n Bool
-- API will not be super easy to use, particularly with the BitVect, but seems thats okay. (actually, reconsidering it, adding a nicer API on top should not be TOO hard, as long as the 'nicer' string has some validator I can use, which should be a given)
module PatriciaTries

import Data.Vect

data Trie : (len : Nat) -> (tVal : Type) -> Type where
  Leaf : (val : tVal) -> Trie 0 tVal
  Left : (l : Trie len tVal) -> Trie (S len) tVal
  Right : (r : Trie len tVal) -> Trie (S len) tVal
  Both : (l : Trie len tVal) -> (r : Trie len tVal) -> Trie (S len) tVal

Key : (len: Nat) -> Type
Key len = Vect len Bool

-- IDK if I did this syntax properly
singleton : {1 len: Nat} -> (key: Key len) -> (val: tVal) -> Trie len tVal
singleton [] val = Leaf val
singleton (x :: xs) val = do
    let remainder = singleton xs val
    case x of
      True => Left remainder
      False => Right remainder

insert : Key len -> tVal -> Trie len tVal -> Trie len tVal
insert key val trie = ?todo

lookup : Key len -> Trie len tVal -> Maybe tVal

union : Trie len tVal -> Trie len tVal -> Trie len tVal

-- todo theoreme
intersection : Trie len tVal -> Trie len tVal -> Trie len tVal

-- my own signature, should be fine
delete: Key len -> Trie len tVal -> Trie len tVal

-- delete: API TODO

theorem1 : (key: Key n) -> (val: tVal) -> (trie: Trie n tVal) -> lookup key (insert key val trie) = Just val

theorem2 : (env: Void) -> union (singleton key val) trie = insert key val trie

-- theoreme das etwas gelöschtes weg ist
theorem_delete_deletes : (env: Void) -> delete key (insert key val trie) = trie

-- TODO: show equivalence of Prefix tree and patricia tree

-- IDK about that, since the last one held the key implicitly with Left and Right, this doesnt really seem to do that, so IDK if the 2nd constructor makes sense
-- also the lenghts might not fit?
-- actually, that is n... is it perhaps just the tree depth?
-- hmmm. also die sache mit diesen prefix trees ist, das deren tiefe von den sets an keys abhängt. Ich glaube nicht das das in einer einfachen API beschreibbar ist...
-- also ist n nachher bloß die anzahl an elementen?
data TrieV2 : (n : Nat) -> (a : Type) -> Type where
  LeafV2 : (keyAdd: Key n) -> (val : a) -> TrieV2 n a
  BothV2 : (keyAdd: Key n) -> (l : TrieV2 m a) -> (r : TrieV2 m a) -> TrieV2 (S(n + m)) a

-- TODO: show equivalence of simple trie (prefix tree) and patricia trie

-- v3, weitergehend: Mache ich irgendwelche speziellen sachen, um die redizierte Entropie von utf-8 auszugleichen (die sich in der form nie ändern wird, z.b. kombinierte codepoints haben viele führende 1en)
-- (check in den haskell impls, ich glaube aber eher nicht)
-- 
-- was ist mit den impls, die einen einzigen String als Key backend nehmen? Das sol zu deutlichen performance verbesserungen führen.
-- vmtl dann v4? (mal schauen, wie einfach das wäre)
