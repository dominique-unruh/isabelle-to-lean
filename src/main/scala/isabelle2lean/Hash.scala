package isabelle2lean

class Hash(val chunk1: Long, val chunk2: Long) {
  override def toString: String = s"$chunk1.$chunk2"

  @inline override def hashCode: Int = chunk1.toInt

  override def equals(that: Any): Boolean = that match
    case that: Hash => chunk1 == that.chunk1 && chunk2 == that.chunk2
}

object Hash {
  def apply(chunks: (Long, Long)) = new Hash(chunks._1, chunks._2)

  val modulus1 = 8081745360848679154L
  val factor1 = 4620898933452264566L
  val modulus2 = 7165180592126960006L
  val factor2 = 7717757225580381391L

  val hashLib: String =
    s"""type hash = LargeWord.word * LargeWord.word
       |val hash0 : hash = (0w0, 0w0)
       |fun hashWord i ((h1,h2) : hash) =
       |  ((h1 * 0w$factor1 + i) mod 0w$modulus1,
       |   (h2 * 0w$factor2 + i) mod 0w$modulus2)
       |
       |(* Warn: does not detect overflow! *)
       |fun hashInt i h = hashWord (LargeWord.fromInt i) h
       |
       |fun hashString str h =
       |  CharVector.foldl (fn (c,h) => hashInt (Char.ord c) h) (hashInt (CharVector.length str) h) str
       |
       |fun hashList (hashFun: 'a -> hash -> hash) xs =
       |  hashInt (length xs) #> fold (hashFun) xs
       |
       |val hashSort = hashList hashString
       |
       |fun hashTyp (Type(name, Ts)) = hashWord 0w1 #> hashString name #> hashList hashTyp Ts
       |  | hashTyp (TFree(name, sort)) = hashWord 0w2 #> hashString name #> hashSort sort
       |  | hashTyp (TVar((name,idx),sort)) = hashWord 0w3 #> hashString name #> hashInt idx #> hashSort sort
       |
       |fun hashAsIntPair hashFun x = let val (h1,h2) = hashFun x hash0 in (LargeWord.toInt h1, LargeWord.toInt h2) end
       |""".stripMargin

}
