# proofs of laws/TwiceReportsRepeatedListLiteral.bend
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/rules/tokens.bend as T
import ../src/syntax/bind.bend as Bind
import ../src/syntax/tree.bend as Tree
import ../src/rules/calls.bend as Calls
import ../src/rules/correctness/pick.bend as Pick
import ../src/rules/correctness/twice.bend as Twice
import ../laws/TwiceReportsRepeatedListLiteral.bend as Laws
import ./lemmas/Nat.bend as M1
import ./lemmas/Pick.bend as M2

# the text of a token, if any
def twice.text(mm: Maybe<&2, Lex.Tok>) -> Maybe<&2, String>:
  match mm:
    case None{}:
      None{}
    case Some{Lex.Tok{k, t, l, c}}:
      Some{t}

# a picked literal token, read by its text
law twice.pick_text:
  for b: Bool
  for kk: Lex.TokKind
  for +t: String
  for l: U32
  for c: U32
  {twice.text(Bool.pick(Maybe<&2, Lex.Tok>, b, Some{Lex.Tok{kk, t, l, c}}, None{})) == Bool.pick(Maybe<&2, String>, b,
      Some{t}, None{}) : Maybe<&2, String>}

def twice.pick_text(b, _kk, _t, _l, _c):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# a pattern opening `Con{..}`, its literal to the rule and to the law
law twice.head_con:
  for kk: Lex.TokKind
  for +tx: String
  for l: U32
  for c: U32
  for op: Lex.Tok
  for ks: Tree.Node
  for cl: Maybe<&2, Lex.Tok>
  for rest: Tree.Node
  {twice.text(Twice.head(Tree.NCons{Tree.Leaf{Lex.Tok{kk, tx, l, c}}, Tree.NCons{Tree.Group{op, ks, cl},
      rest}})) == Laws.twice.first(Tree.NCons{Tree.Leaf{Lex.Tok{kk, tx, l, c}}, Tree.NCons{Tree.Group{op, ks, cl},
      rest}}) : Maybe<&2, String>}

def twice.head_con(kk, tx, _l, _c, _op, ks, _cl, _rest):
  match kk:
    case Lex.TName{}:
      {==}
    case Lex.TUpper{}:
      match ks:
        case Tree.Leaf{Lex.Tok{+k433, +x434, +l435, +c436}}:
          {==}
        case Tree.Group{+op437, +ks438, +cl439}:
          {==}
        case Tree.Stmt{+sk440, +sks441, +sb442}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{+h443, +t444}:
          match h443:
            case Tree.Leaf{Lex.Tok{+k445, +x446, +l447, +c448}}:
              twice.pick_text(Bool.and(String.eq(tx, "Con"), T.is_lit(k445)), k445, x446, l447, c448)
            case Tree.Group{+op449, +ks450, +cl451}:
              {==}
            case Tree.Stmt{+sk452, +sks453, +sb454}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{+h455, +t456}:
              {==}
    case Lex.TDotted{}:
      {==}
    case Lex.TWild{}:
      {==}
    case Lex.TKey{}:
      {==}
    case Lex.TNum{}:
      {==}
    case Lex.TStr{}:
      {==}
    case Lex.TChar{}:
      {==}
    case Lex.TComment{}:
      {==}
    case Lex.TSpace{}:
      {==}
    case Lex.TNewline{}:
      {==}
    case Lex.TOp{}:
      {==}
    case Lex.TColon{}:
      {==}
    case Lex.TEq{}:
      {==}
    case Lex.TBind{}:
      {==}
    case Lex.TArrow{}:
      {==}
    case Lex.TLam{}:
      {==}
    case Lex.TAll{}:
      {==}
    case Lex.TAmp{}:
      {==}
    case Lex.TOpen{}:
      {==}
    case Lex.TClose{}:
      {==}
    case Lex.TComma{}:
      {==}

# a pattern opening with a token, its literal to the rule and to the law
law twice.head2:
  for kk: Lex.TokKind
  for +tx: String
  for +l: U32
  for +c: U32
  for +t: Tree.Node
  {twice.text(Twice.head(Tree.NCons{Tree.Leaf{Lex.Tok{kk, tx, l, c}},
      t})) == Laws.twice.first(Tree.NCons{Tree.Leaf{Lex.Tok{kk, tx, l, c}}, t}) : Maybe<&2, String>}

def twice.head2(kk, tx, l, c, t):
  match kk:
    case Lex.TName{}:
      match t:
        case Tree.Leaf{Lex.Tok{+k457, +x458, +l459, +c460}}:
          {==}
        case Tree.Group{+op461, +ks462, +cl463}:
          {==}
        case Tree.Stmt{+sk464, +sks465, +sb466}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{+h467, +t468}:
          match h467:
            case Tree.Leaf{Lex.Tok{+k469, +x470, +l471, +c472}}:
              twice.pick_text(Bool.and(T.is_lit(Lex.TName{}), String.eq(x470, "<>")), Lex.TName{}, tx, l, c)
            case Tree.Group{+op473, +ks474, +cl475}:
              twice.head_con(Lex.TName{}, tx, l, c, op473, ks474, cl475, t468)
            case Tree.Stmt{+sk476, +sks477, +sb478}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{+h479, +t480}:
              {==}
    case Lex.TUpper{}:
      match t:
        case Tree.Leaf{Lex.Tok{+k481, +x482, +l483, +c484}}:
          {==}
        case Tree.Group{+op485, +ks486, +cl487}:
          {==}
        case Tree.Stmt{+sk488, +sks489, +sb490}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{+h491, +t492}:
          match h491:
            case Tree.Leaf{Lex.Tok{+k493, +x494, +l495, +c496}}:
              twice.pick_text(Bool.and(T.is_lit(Lex.TUpper{}), String.eq(x494, "<>")), Lex.TUpper{}, tx, l, c)
            case Tree.Group{+op497, +ks498, +cl499}:
              twice.head_con(Lex.TUpper{}, tx, l, c, op497, ks498, cl499, t492)
            case Tree.Stmt{+sk500, +sks501, +sb502}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{+h503, +t504}:
              {==}
    case Lex.TDotted{}:
      match t:
        case Tree.Leaf{Lex.Tok{+k505, +x506, +l507, +c508}}:
          {==}
        case Tree.Group{+op509, +ks510, +cl511}:
          {==}
        case Tree.Stmt{+sk512, +sks513, +sb514}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{+h515, +t516}:
          match h515:
            case Tree.Leaf{Lex.Tok{+k517, +x518, +l519, +c520}}:
              twice.pick_text(Bool.and(T.is_lit(Lex.TDotted{}), String.eq(x518, "<>")), Lex.TDotted{}, tx, l, c)
            case Tree.Group{+op521, +ks522, +cl523}:
              twice.head_con(Lex.TDotted{}, tx, l, c, op521, ks522, cl523, t516)
            case Tree.Stmt{+sk524, +sks525, +sb526}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{+h527, +t528}:
              {==}
    case Lex.TWild{}:
      match t:
        case Tree.Leaf{Lex.Tok{+k529, +x530, +l531, +c532}}:
          {==}
        case Tree.Group{+op533, +ks534, +cl535}:
          {==}
        case Tree.Stmt{+sk536, +sks537, +sb538}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{+h539, +t540}:
          match h539:
            case Tree.Leaf{Lex.Tok{+k541, +x542, +l543, +c544}}:
              twice.pick_text(Bool.and(T.is_lit(Lex.TWild{}), String.eq(x542, "<>")), Lex.TWild{}, tx, l, c)
            case Tree.Group{+op545, +ks546, +cl547}:
              twice.head_con(Lex.TWild{}, tx, l, c, op545, ks546, cl547, t540)
            case Tree.Stmt{+sk548, +sks549, +sb550}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{+h551, +t552}:
              {==}
    case Lex.TKey{}:
      match t:
        case Tree.Leaf{Lex.Tok{+k553, +x554, +l555, +c556}}:
          {==}
        case Tree.Group{+op557, +ks558, +cl559}:
          {==}
        case Tree.Stmt{+sk560, +sks561, +sb562}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{+h563, +t564}:
          match h563:
            case Tree.Leaf{Lex.Tok{+k565, +x566, +l567, +c568}}:
              twice.pick_text(Bool.and(T.is_lit(Lex.TKey{}), String.eq(x566, "<>")), Lex.TKey{}, tx, l, c)
            case Tree.Group{+op569, +ks570, +cl571}:
              twice.head_con(Lex.TKey{}, tx, l, c, op569, ks570, cl571, t564)
            case Tree.Stmt{+sk572, +sks573, +sb574}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{+h575, +t576}:
              {==}
    case Lex.TNum{}:
      match t:
        case Tree.Leaf{Lex.Tok{+k577, +x578, +l579, +c580}}:
          {==}
        case Tree.Group{+op581, +ks582, +cl583}:
          {==}
        case Tree.Stmt{+sk584, +sks585, +sb586}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{+h587, +t588}:
          match h587:
            case Tree.Leaf{Lex.Tok{+k589, +x590, +l591, +c592}}:
              twice.pick_text(Bool.and(T.is_lit(Lex.TNum{}), String.eq(x590, "<>")), Lex.TNum{}, tx, l, c)
            case Tree.Group{+op593, +ks594, +cl595}:
              twice.head_con(Lex.TNum{}, tx, l, c, op593, ks594, cl595, t588)
            case Tree.Stmt{+sk596, +sks597, +sb598}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{+h599, +t600}:
              {==}
    case Lex.TStr{}:
      match t:
        case Tree.Leaf{Lex.Tok{+k601, +x602, +l603, +c604}}:
          {==}
        case Tree.Group{+op605, +ks606, +cl607}:
          {==}
        case Tree.Stmt{+sk608, +sks609, +sb610}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{+h611, +t612}:
          match h611:
            case Tree.Leaf{Lex.Tok{+k613, +x614, +l615, +c616}}:
              twice.pick_text(Bool.and(T.is_lit(Lex.TStr{}), String.eq(x614, "<>")), Lex.TStr{}, tx, l, c)
            case Tree.Group{+op617, +ks618, +cl619}:
              twice.head_con(Lex.TStr{}, tx, l, c, op617, ks618, cl619, t612)
            case Tree.Stmt{+sk620, +sks621, +sb622}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{+h623, +t624}:
              {==}
    case Lex.TChar{}:
      match t:
        case Tree.Leaf{Lex.Tok{+k625, +x626, +l627, +c628}}:
          {==}
        case Tree.Group{+op629, +ks630, +cl631}:
          {==}
        case Tree.Stmt{+sk632, +sks633, +sb634}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{+h635, +t636}:
          match h635:
            case Tree.Leaf{Lex.Tok{+k637, +x638, +l639, +c640}}:
              twice.pick_text(Bool.and(T.is_lit(Lex.TChar{}), String.eq(x638, "<>")), Lex.TChar{}, tx, l, c)
            case Tree.Group{+op641, +ks642, +cl643}:
              twice.head_con(Lex.TChar{}, tx, l, c, op641, ks642, cl643, t636)
            case Tree.Stmt{+sk644, +sks645, +sb646}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{+h647, +t648}:
              {==}
    case Lex.TComment{}:
      match t:
        case Tree.Leaf{Lex.Tok{+k649, +x650, +l651, +c652}}:
          {==}
        case Tree.Group{+op653, +ks654, +cl655}:
          {==}
        case Tree.Stmt{+sk656, +sks657, +sb658}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{+h659, +t660}:
          match h659:
            case Tree.Leaf{Lex.Tok{+k661, +x662, +l663, +c664}}:
              twice.pick_text(Bool.and(T.is_lit(Lex.TComment{}), String.eq(x662, "<>")), Lex.TComment{}, tx, l, c)
            case Tree.Group{+op665, +ks666, +cl667}:
              twice.head_con(Lex.TComment{}, tx, l, c, op665, ks666, cl667, t660)
            case Tree.Stmt{+sk668, +sks669, +sb670}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{+h671, +t672}:
              {==}
    case Lex.TSpace{}:
      match t:
        case Tree.Leaf{Lex.Tok{+k673, +x674, +l675, +c676}}:
          {==}
        case Tree.Group{+op677, +ks678, +cl679}:
          {==}
        case Tree.Stmt{+sk680, +sks681, +sb682}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{+h683, +t684}:
          match h683:
            case Tree.Leaf{Lex.Tok{+k685, +x686, +l687, +c688}}:
              twice.pick_text(Bool.and(T.is_lit(Lex.TSpace{}), String.eq(x686, "<>")), Lex.TSpace{}, tx, l, c)
            case Tree.Group{+op689, +ks690, +cl691}:
              twice.head_con(Lex.TSpace{}, tx, l, c, op689, ks690, cl691, t684)
            case Tree.Stmt{+sk692, +sks693, +sb694}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{+h695, +t696}:
              {==}
    case Lex.TNewline{}:
      match t:
        case Tree.Leaf{Lex.Tok{+k697, +x698, +l699, +c700}}:
          {==}
        case Tree.Group{+op701, +ks702, +cl703}:
          {==}
        case Tree.Stmt{+sk704, +sks705, +sb706}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{+h707, +t708}:
          match h707:
            case Tree.Leaf{Lex.Tok{+k709, +x710, +l711, +c712}}:
              twice.pick_text(Bool.and(T.is_lit(Lex.TNewline{}), String.eq(x710, "<>")), Lex.TNewline{}, tx, l, c)
            case Tree.Group{+op713, +ks714, +cl715}:
              twice.head_con(Lex.TNewline{}, tx, l, c, op713, ks714, cl715, t708)
            case Tree.Stmt{+sk716, +sks717, +sb718}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{+h719, +t720}:
              {==}
    case Lex.TOp{}:
      match t:
        case Tree.Leaf{Lex.Tok{+k721, +x722, +l723, +c724}}:
          {==}
        case Tree.Group{+op725, +ks726, +cl727}:
          {==}
        case Tree.Stmt{+sk728, +sks729, +sb730}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{+h731, +t732}:
          match h731:
            case Tree.Leaf{Lex.Tok{+k733, +x734, +l735, +c736}}:
              twice.pick_text(Bool.and(T.is_lit(Lex.TOp{}), String.eq(x734, "<>")), Lex.TOp{}, tx, l, c)
            case Tree.Group{+op737, +ks738, +cl739}:
              twice.head_con(Lex.TOp{}, tx, l, c, op737, ks738, cl739, t732)
            case Tree.Stmt{+sk740, +sks741, +sb742}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{+h743, +t744}:
              {==}
    case Lex.TColon{}:
      match t:
        case Tree.Leaf{Lex.Tok{+k745, +x746, +l747, +c748}}:
          {==}
        case Tree.Group{+op749, +ks750, +cl751}:
          {==}
        case Tree.Stmt{+sk752, +sks753, +sb754}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{+h755, +t756}:
          match h755:
            case Tree.Leaf{Lex.Tok{+k757, +x758, +l759, +c760}}:
              twice.pick_text(Bool.and(T.is_lit(Lex.TColon{}), String.eq(x758, "<>")), Lex.TColon{}, tx, l, c)
            case Tree.Group{+op761, +ks762, +cl763}:
              twice.head_con(Lex.TColon{}, tx, l, c, op761, ks762, cl763, t756)
            case Tree.Stmt{+sk764, +sks765, +sb766}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{+h767, +t768}:
              {==}
    case Lex.TEq{}:
      match t:
        case Tree.Leaf{Lex.Tok{+k769, +x770, +l771, +c772}}:
          {==}
        case Tree.Group{+op773, +ks774, +cl775}:
          {==}
        case Tree.Stmt{+sk776, +sks777, +sb778}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{+h779, +t780}:
          match h779:
            case Tree.Leaf{Lex.Tok{+k781, +x782, +l783, +c784}}:
              twice.pick_text(Bool.and(T.is_lit(Lex.TEq{}), String.eq(x782, "<>")), Lex.TEq{}, tx, l, c)
            case Tree.Group{+op785, +ks786, +cl787}:
              twice.head_con(Lex.TEq{}, tx, l, c, op785, ks786, cl787, t780)
            case Tree.Stmt{+sk788, +sks789, +sb790}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{+h791, +t792}:
              {==}
    case Lex.TBind{}:
      match t:
        case Tree.Leaf{Lex.Tok{+k793, +x794, +l795, +c796}}:
          {==}
        case Tree.Group{+op797, +ks798, +cl799}:
          {==}
        case Tree.Stmt{+sk800, +sks801, +sb802}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{+h803, +t804}:
          match h803:
            case Tree.Leaf{Lex.Tok{+k805, +x806, +l807, +c808}}:
              twice.pick_text(Bool.and(T.is_lit(Lex.TBind{}), String.eq(x806, "<>")), Lex.TBind{}, tx, l, c)
            case Tree.Group{+op809, +ks810, +cl811}:
              twice.head_con(Lex.TBind{}, tx, l, c, op809, ks810, cl811, t804)
            case Tree.Stmt{+sk812, +sks813, +sb814}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{+h815, +t816}:
              {==}
    case Lex.TArrow{}:
      match t:
        case Tree.Leaf{Lex.Tok{+k817, +x818, +l819, +c820}}:
          {==}
        case Tree.Group{+op821, +ks822, +cl823}:
          {==}
        case Tree.Stmt{+sk824, +sks825, +sb826}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{+h827, +t828}:
          match h827:
            case Tree.Leaf{Lex.Tok{+k829, +x830, +l831, +c832}}:
              twice.pick_text(Bool.and(T.is_lit(Lex.TArrow{}), String.eq(x830, "<>")), Lex.TArrow{}, tx, l, c)
            case Tree.Group{+op833, +ks834, +cl835}:
              twice.head_con(Lex.TArrow{}, tx, l, c, op833, ks834, cl835, t828)
            case Tree.Stmt{+sk836, +sks837, +sb838}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{+h839, +t840}:
              {==}
    case Lex.TLam{}:
      match t:
        case Tree.Leaf{Lex.Tok{+k841, +x842, +l843, +c844}}:
          {==}
        case Tree.Group{+op845, +ks846, +cl847}:
          {==}
        case Tree.Stmt{+sk848, +sks849, +sb850}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{+h851, +t852}:
          match h851:
            case Tree.Leaf{Lex.Tok{+k853, +x854, +l855, +c856}}:
              twice.pick_text(Bool.and(T.is_lit(Lex.TLam{}), String.eq(x854, "<>")), Lex.TLam{}, tx, l, c)
            case Tree.Group{+op857, +ks858, +cl859}:
              twice.head_con(Lex.TLam{}, tx, l, c, op857, ks858, cl859, t852)
            case Tree.Stmt{+sk860, +sks861, +sb862}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{+h863, +t864}:
              {==}
    case Lex.TAll{}:
      match t:
        case Tree.Leaf{Lex.Tok{+k865, +x866, +l867, +c868}}:
          {==}
        case Tree.Group{+op869, +ks870, +cl871}:
          {==}
        case Tree.Stmt{+sk872, +sks873, +sb874}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{+h875, +t876}:
          match h875:
            case Tree.Leaf{Lex.Tok{+k877, +x878, +l879, +c880}}:
              twice.pick_text(Bool.and(T.is_lit(Lex.TAll{}), String.eq(x878, "<>")), Lex.TAll{}, tx, l, c)
            case Tree.Group{+op881, +ks882, +cl883}:
              twice.head_con(Lex.TAll{}, tx, l, c, op881, ks882, cl883, t876)
            case Tree.Stmt{+sk884, +sks885, +sb886}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{+h887, +t888}:
              {==}
    case Lex.TAmp{}:
      match t:
        case Tree.Leaf{Lex.Tok{+k889, +x890, +l891, +c892}}:
          {==}
        case Tree.Group{+op893, +ks894, +cl895}:
          {==}
        case Tree.Stmt{+sk896, +sks897, +sb898}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{+h899, +t900}:
          match h899:
            case Tree.Leaf{Lex.Tok{+k901, +x902, +l903, +c904}}:
              twice.pick_text(Bool.and(T.is_lit(Lex.TAmp{}), String.eq(x902, "<>")), Lex.TAmp{}, tx, l, c)
            case Tree.Group{+op905, +ks906, +cl907}:
              twice.head_con(Lex.TAmp{}, tx, l, c, op905, ks906, cl907, t900)
            case Tree.Stmt{+sk908, +sks909, +sb910}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{+h911, +t912}:
              {==}
    case Lex.TOpen{}:
      match t:
        case Tree.Leaf{Lex.Tok{+k913, +x914, +l915, +c916}}:
          {==}
        case Tree.Group{+op917, +ks918, +cl919}:
          {==}
        case Tree.Stmt{+sk920, +sks921, +sb922}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{+h923, +t924}:
          match h923:
            case Tree.Leaf{Lex.Tok{+k925, +x926, +l927, +c928}}:
              twice.pick_text(Bool.and(T.is_lit(Lex.TOpen{}), String.eq(x926, "<>")), Lex.TOpen{}, tx, l, c)
            case Tree.Group{+op929, +ks930, +cl931}:
              twice.head_con(Lex.TOpen{}, tx, l, c, op929, ks930, cl931, t924)
            case Tree.Stmt{+sk932, +sks933, +sb934}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{+h935, +t936}:
              {==}
    case Lex.TClose{}:
      match t:
        case Tree.Leaf{Lex.Tok{+k937, +x938, +l939, +c940}}:
          {==}
        case Tree.Group{+op941, +ks942, +cl943}:
          {==}
        case Tree.Stmt{+sk944, +sks945, +sb946}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{+h947, +t948}:
          match h947:
            case Tree.Leaf{Lex.Tok{+k949, +x950, +l951, +c952}}:
              twice.pick_text(Bool.and(T.is_lit(Lex.TClose{}), String.eq(x950, "<>")), Lex.TClose{}, tx, l, c)
            case Tree.Group{+op953, +ks954, +cl955}:
              twice.head_con(Lex.TClose{}, tx, l, c, op953, ks954, cl955, t948)
            case Tree.Stmt{+sk956, +sks957, +sb958}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{+h959, +t960}:
              {==}
    case Lex.TComma{}:
      match t:
        case Tree.Leaf{Lex.Tok{+k961, +x962, +l963, +c964}}:
          {==}
        case Tree.Group{+op965, +ks966, +cl967}:
          {==}
        case Tree.Stmt{+sk968, +sks969, +sb970}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{+h971, +t972}:
          match h971:
            case Tree.Leaf{Lex.Tok{+k973, +x974, +l975, +c976}}:
              twice.pick_text(Bool.and(T.is_lit(Lex.TComma{}), String.eq(x974, "<>")), Lex.TComma{}, tx, l, c)
            case Tree.Group{+op977, +ks978, +cl979}:
              twice.head_con(Lex.TComma{}, tx, l, c, op977, ks978, cl979, t972)
            case Tree.Stmt{+sk980, +sks981, +sb982}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{+h983, +t984}:
              {==}

# the literal a list pattern opens with, to the rule and to the law
law twice.head:
  for pat: Tree.Node
  {twice.text(Twice.head(pat)) == Laws.twice.first(pat) : Maybe<&2, String>}

def twice.head(pat):
  match pat:
    case Tree.Leaf{Lex.Tok{+k985, +x986, +l987, +c988}}:
      {==}
    case Tree.Group{+op989, +ks990, +cl991}:
      {==}
    case Tree.Stmt{+sk992, +sks993, +sb994}:
      {==}
    case Tree.NNil{}:
      {==}
    case Tree.NCons{+h995, +t996}:
      match h995:
        case Tree.Leaf{Lex.Tok{+k997, +x998, +l999, +c1000}}:
          twice.head2(k997, x998, l999, c1000, t996)
        case Tree.Group{+op1001, +ks1002, +cl1003}:
          match t996:
            case Tree.Leaf{Lex.Tok{+k1004, +x1005, +l1006, +c1007}}:
              {==}
            case Tree.Group{+op1008, +ks1009, +cl1010}:
              {==}
            case Tree.Stmt{+sk1011, +sks1012, +sb1013}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{+h1014, +t1015}:
              {==}
        case Tree.Stmt{+sk1016, +sks1017, +sb1018}:
          match t996:
            case Tree.Leaf{Lex.Tok{+k1019, +x1020, +l1021, +c1022}}:
              {==}
            case Tree.Group{+op1023, +ks1024, +cl1025}:
              {==}
            case Tree.Stmt{+sk1026, +sks1027, +sb1028}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{+h1029, +t1030}:
              {==}
        case Tree.NNil{}:
          match t996:
            case Tree.Leaf{Lex.Tok{+k1031, +x1032, +l1033, +c1034}}:
              {==}
            case Tree.Group{+op1035, +ks1036, +cl1037}:
              {==}
            case Tree.Stmt{+sk1038, +sks1039, +sb1040}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{+h1041, +t1042}:
              {==}
        case Tree.NCons{+h1043, +t1044}:
          match t996:
            case Tree.Leaf{Lex.Tok{+k1045, +x1046, +l1047, +c1048}}:
              {==}
            case Tree.Group{+op1049, +ks1050, +cl1051}:
              {==}
            case Tree.Stmt{+sk1052, +sks1053, +sb1054}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{+h1055, +t1056}:
              {==}

# a list pattern past its first element, to the rule and to the law
law twice.tail:
  for pat: Tree.Node
  {Twice.tail(pat) == Laws.twice.after(pat) : Tree.Node}

def twice.tail(pat):
  match pat:
    case Tree.Leaf{Lex.Tok{+k1057, +x1058, +l1059, +c1060}}:
      {==}
    case Tree.Group{+op1061, +ks1062, +cl1063}:
      {==}
    case Tree.Stmt{+sk1064, +sks1065, +sb1066}:
      {==}
    case Tree.NNil{}:
      {==}
    case Tree.NCons{+h1067, +t1068}:
      match h1067:
        case Tree.Leaf{Lex.Tok{+k1069, +x1070, +l1071, +c1072}}:
          match k1069:
            case Lex.TName{}:
              match t1068:
                case Tree.Leaf{Lex.Tok{+k1073, +x1074, +l1075, +c1076}}:
                  {==}
                case Tree.Group{+op1077, +ks1078, +cl1079}:
                  {==}
                case Tree.Stmt{+sk1080, +sks1081, +sb1082}:
                  {==}
                case Tree.NNil{}:
                  {==}
                case Tree.NCons{+h1083, +t1084}:
                  {==}
            case Lex.TUpper{}:
              match t1068:
                case Tree.Leaf{Lex.Tok{+k1085, +x1086, +l1087, +c1088}}:
                  {==}
                case Tree.Group{+op1089, +ks1090, +cl1091}:
                  {==}
                case Tree.Stmt{+sk1092, +sks1093, +sb1094}:
                  {==}
                case Tree.NNil{}:
                  {==}
                case Tree.NCons{+h1095, +t1096}:
                  match h1095:
                    case Tree.Leaf{Lex.Tok{+k1097, +x1098, +l1099, +c1100}}:
                      {==}
                    case Tree.Group{+op1101, +ks1102, +cl1103}:
                      match ks1102:
                        case Tree.Leaf{Lex.Tok{+k1104, +x1105, +l1106, +c1107}}:
                          {==}
                        case Tree.Group{+op1108, +ks1109, +cl1110}:
                          {==}
                        case Tree.Stmt{+sk1111, +sks1112, +sb1113}:
                          {==}
                        case Tree.NNil{}:
                          {==}
                        case Tree.NCons{+h1114, +t1115}:
                          match t1115:
                            case Tree.Leaf{Lex.Tok{+k1116, +x1117, +l1118, +c1119}}:
                              {==}
                            case Tree.Group{+op1120, +ks1121, +cl1122}:
                              {==}
                            case Tree.Stmt{+sk1123, +sks1124, +sb1125}:
                              {==}
                            case Tree.NNil{}:
                              {==}
                            case Tree.NCons{+h1126, +t1127}:
                              {==}
                    case Tree.Stmt{+sk1128, +sks1129, +sb1130}:
                      {==}
                    case Tree.NNil{}:
                      {==}
                    case Tree.NCons{+h1131, +t1132}:
                      {==}
            case Lex.TDotted{}:
              match t1068:
                case Tree.Leaf{Lex.Tok{+k1133, +x1134, +l1135, +c1136}}:
                  {==}
                case Tree.Group{+op1137, +ks1138, +cl1139}:
                  {==}
                case Tree.Stmt{+sk1140, +sks1141, +sb1142}:
                  {==}
                case Tree.NNil{}:
                  {==}
                case Tree.NCons{+h1143, +t1144}:
                  {==}
            case Lex.TWild{}:
              match t1068:
                case Tree.Leaf{Lex.Tok{+k1145, +x1146, +l1147, +c1148}}:
                  {==}
                case Tree.Group{+op1149, +ks1150, +cl1151}:
                  {==}
                case Tree.Stmt{+sk1152, +sks1153, +sb1154}:
                  {==}
                case Tree.NNil{}:
                  {==}
                case Tree.NCons{+h1155, +t1156}:
                  {==}
            case Lex.TKey{}:
              match t1068:
                case Tree.Leaf{Lex.Tok{+k1157, +x1158, +l1159, +c1160}}:
                  {==}
                case Tree.Group{+op1161, +ks1162, +cl1163}:
                  {==}
                case Tree.Stmt{+sk1164, +sks1165, +sb1166}:
                  {==}
                case Tree.NNil{}:
                  {==}
                case Tree.NCons{+h1167, +t1168}:
                  {==}
            case Lex.TNum{}:
              match t1068:
                case Tree.Leaf{Lex.Tok{+k1169, +x1170, +l1171, +c1172}}:
                  {==}
                case Tree.Group{+op1173, +ks1174, +cl1175}:
                  {==}
                case Tree.Stmt{+sk1176, +sks1177, +sb1178}:
                  {==}
                case Tree.NNil{}:
                  {==}
                case Tree.NCons{+h1179, +t1180}:
                  {==}
            case Lex.TStr{}:
              match t1068:
                case Tree.Leaf{Lex.Tok{+k1181, +x1182, +l1183, +c1184}}:
                  {==}
                case Tree.Group{+op1185, +ks1186, +cl1187}:
                  {==}
                case Tree.Stmt{+sk1188, +sks1189, +sb1190}:
                  {==}
                case Tree.NNil{}:
                  {==}
                case Tree.NCons{+h1191, +t1192}:
                  {==}
            case Lex.TChar{}:
              match t1068:
                case Tree.Leaf{Lex.Tok{+k1193, +x1194, +l1195, +c1196}}:
                  {==}
                case Tree.Group{+op1197, +ks1198, +cl1199}:
                  {==}
                case Tree.Stmt{+sk1200, +sks1201, +sb1202}:
                  {==}
                case Tree.NNil{}:
                  {==}
                case Tree.NCons{+h1203, +t1204}:
                  {==}
            case Lex.TComment{}:
              match t1068:
                case Tree.Leaf{Lex.Tok{+k1205, +x1206, +l1207, +c1208}}:
                  {==}
                case Tree.Group{+op1209, +ks1210, +cl1211}:
                  {==}
                case Tree.Stmt{+sk1212, +sks1213, +sb1214}:
                  {==}
                case Tree.NNil{}:
                  {==}
                case Tree.NCons{+h1215, +t1216}:
                  {==}
            case Lex.TSpace{}:
              match t1068:
                case Tree.Leaf{Lex.Tok{+k1217, +x1218, +l1219, +c1220}}:
                  {==}
                case Tree.Group{+op1221, +ks1222, +cl1223}:
                  {==}
                case Tree.Stmt{+sk1224, +sks1225, +sb1226}:
                  {==}
                case Tree.NNil{}:
                  {==}
                case Tree.NCons{+h1227, +t1228}:
                  {==}
            case Lex.TNewline{}:
              match t1068:
                case Tree.Leaf{Lex.Tok{+k1229, +x1230, +l1231, +c1232}}:
                  {==}
                case Tree.Group{+op1233, +ks1234, +cl1235}:
                  {==}
                case Tree.Stmt{+sk1236, +sks1237, +sb1238}:
                  {==}
                case Tree.NNil{}:
                  {==}
                case Tree.NCons{+h1239, +t1240}:
                  {==}
            case Lex.TOp{}:
              match t1068:
                case Tree.Leaf{Lex.Tok{+k1241, +x1242, +l1243, +c1244}}:
                  {==}
                case Tree.Group{+op1245, +ks1246, +cl1247}:
                  {==}
                case Tree.Stmt{+sk1248, +sks1249, +sb1250}:
                  {==}
                case Tree.NNil{}:
                  {==}
                case Tree.NCons{+h1251, +t1252}:
                  {==}
            case Lex.TColon{}:
              match t1068:
                case Tree.Leaf{Lex.Tok{+k1253, +x1254, +l1255, +c1256}}:
                  {==}
                case Tree.Group{+op1257, +ks1258, +cl1259}:
                  {==}
                case Tree.Stmt{+sk1260, +sks1261, +sb1262}:
                  {==}
                case Tree.NNil{}:
                  {==}
                case Tree.NCons{+h1263, +t1264}:
                  {==}
            case Lex.TEq{}:
              match t1068:
                case Tree.Leaf{Lex.Tok{+k1265, +x1266, +l1267, +c1268}}:
                  {==}
                case Tree.Group{+op1269, +ks1270, +cl1271}:
                  {==}
                case Tree.Stmt{+sk1272, +sks1273, +sb1274}:
                  {==}
                case Tree.NNil{}:
                  {==}
                case Tree.NCons{+h1275, +t1276}:
                  {==}
            case Lex.TBind{}:
              match t1068:
                case Tree.Leaf{Lex.Tok{+k1277, +x1278, +l1279, +c1280}}:
                  {==}
                case Tree.Group{+op1281, +ks1282, +cl1283}:
                  {==}
                case Tree.Stmt{+sk1284, +sks1285, +sb1286}:
                  {==}
                case Tree.NNil{}:
                  {==}
                case Tree.NCons{+h1287, +t1288}:
                  {==}
            case Lex.TArrow{}:
              match t1068:
                case Tree.Leaf{Lex.Tok{+k1289, +x1290, +l1291, +c1292}}:
                  {==}
                case Tree.Group{+op1293, +ks1294, +cl1295}:
                  {==}
                case Tree.Stmt{+sk1296, +sks1297, +sb1298}:
                  {==}
                case Tree.NNil{}:
                  {==}
                case Tree.NCons{+h1299, +t1300}:
                  {==}
            case Lex.TLam{}:
              match t1068:
                case Tree.Leaf{Lex.Tok{+k1301, +x1302, +l1303, +c1304}}:
                  {==}
                case Tree.Group{+op1305, +ks1306, +cl1307}:
                  {==}
                case Tree.Stmt{+sk1308, +sks1309, +sb1310}:
                  {==}
                case Tree.NNil{}:
                  {==}
                case Tree.NCons{+h1311, +t1312}:
                  {==}
            case Lex.TAll{}:
              match t1068:
                case Tree.Leaf{Lex.Tok{+k1313, +x1314, +l1315, +c1316}}:
                  {==}
                case Tree.Group{+op1317, +ks1318, +cl1319}:
                  {==}
                case Tree.Stmt{+sk1320, +sks1321, +sb1322}:
                  {==}
                case Tree.NNil{}:
                  {==}
                case Tree.NCons{+h1323, +t1324}:
                  {==}
            case Lex.TAmp{}:
              match t1068:
                case Tree.Leaf{Lex.Tok{+k1325, +x1326, +l1327, +c1328}}:
                  {==}
                case Tree.Group{+op1329, +ks1330, +cl1331}:
                  {==}
                case Tree.Stmt{+sk1332, +sks1333, +sb1334}:
                  {==}
                case Tree.NNil{}:
                  {==}
                case Tree.NCons{+h1335, +t1336}:
                  {==}
            case Lex.TOpen{}:
              match t1068:
                case Tree.Leaf{Lex.Tok{+k1337, +x1338, +l1339, +c1340}}:
                  {==}
                case Tree.Group{+op1341, +ks1342, +cl1343}:
                  {==}
                case Tree.Stmt{+sk1344, +sks1345, +sb1346}:
                  {==}
                case Tree.NNil{}:
                  {==}
                case Tree.NCons{+h1347, +t1348}:
                  {==}
            case Lex.TClose{}:
              match t1068:
                case Tree.Leaf{Lex.Tok{+k1349, +x1350, +l1351, +c1352}}:
                  {==}
                case Tree.Group{+op1353, +ks1354, +cl1355}:
                  {==}
                case Tree.Stmt{+sk1356, +sks1357, +sb1358}:
                  {==}
                case Tree.NNil{}:
                  {==}
                case Tree.NCons{+h1359, +t1360}:
                  {==}
            case Lex.TComma{}:
              match t1068:
                case Tree.Leaf{Lex.Tok{+k1361, +x1362, +l1363, +c1364}}:
                  {==}
                case Tree.Group{+op1365, +ks1366, +cl1367}:
                  {==}
                case Tree.Stmt{+sk1368, +sks1369, +sb1370}:
                  {==}
                case Tree.NNil{}:
                  {==}
                case Tree.NCons{+h1371, +t1372}:
                  {==}
        case Tree.Group{+op1373, +ks1374, +cl1375}:
          match t1068:
            case Tree.Leaf{Lex.Tok{+k1376, +x1377, +l1378, +c1379}}:
              {==}
            case Tree.Group{+op1380, +ks1381, +cl1382}:
              {==}
            case Tree.Stmt{+sk1383, +sks1384, +sb1385}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{+h1386, +t1387}:
              {==}
        case Tree.Stmt{+sk1388, +sks1389, +sb1390}:
          match t1068:
            case Tree.Leaf{Lex.Tok{+k1391, +x1392, +l1393, +c1394}}:
              {==}
            case Tree.Group{+op1395, +ks1396, +cl1397}:
              {==}
            case Tree.Stmt{+sk1398, +sks1399, +sb1400}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{+h1401, +t1402}:
              {==}
        case Tree.NNil{}:
          match t1068:
            case Tree.Leaf{Lex.Tok{+k1403, +x1404, +l1405, +c1406}}:
              {==}
            case Tree.Group{+op1407, +ks1408, +cl1409}:
              {==}
            case Tree.Stmt{+sk1410, +sks1411, +sb1412}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{+h1413, +t1414}:
              {==}
        case Tree.NCons{+h1415, +t1416}:
          match t1068:
            case Tree.Leaf{Lex.Tok{+k1417, +x1418, +l1419, +c1420}}:
              {==}
            case Tree.Group{+op1421, +ks1422, +cl1423}:
              {==}
            case Tree.Stmt{+sk1424, +sks1425, +sb1426}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{+h1427, +t1428}:
              {==}

# a literal against a second, a finding exactly when the law's same
law twice.same2:
  for k: Lex.TokKind
  for +t: String
  for l: U32
  for c: U32
  for bb: Maybe<&2, Lex.Tok>
  for +path: String
  {List.length(&2, F.Finding, Twice.same(Some{Lex.Tok{k, t, l, c}}, bb, path)) == Bool.pick(Nat,
      Laws.twice.same(Some{t}, twice.text(bb)), 1n, 0n) : Nat}

def twice.same2(_k, t, _l, _c, bb, path):
  match bb:
    case None{}:
      {==}
    case Some{Lex.Tok{k2, +t2, +l2, +c2}}:
      M1.nat.pick(String.eq(t, t2), F.Finding{path, l2, c2, T.width(t2), "twice",
        "This literal appears twice in one list pattern, which makes the checker hang; match one element per step."},
          [], 0n, {==})

# two literals, a finding exactly when the law's same
law twice.same:
  for aa: Maybe<&2, Lex.Tok>
  for bb: Maybe<&2, Lex.Tok>
  for +path: String
  {List.length(&2, F.Finding, Twice.same(aa, bb, path)) == Bool.pick(Nat, Laws.twice.same(twice.text(aa),
      twice.text(bb)), 1n, 0n) : Nat}

def twice.same(aa, bb, path):
  match aa:
    case None{}:
      {==}
    case Some{Lex.Tok{k, t, l, c}}:
      twice.same2(k, t, l, c, bb, path)

# a case pattern, a finding exactly when it opens with the same literal twice
law twice.arm:
  for +pat: Tree.Node
  for +path: String
  {List.length(&2, F.Finding, Twice.arm(pat, path)) == Bool.pick(Nat, Laws.twice.same(Laws.twice.first(pat),
      Laws.twice.first(Laws.twice.after(pat))), 1n, 0n) : Nat}

def twice.arm(pat, path):
  Equal.trans(Nat, List.length(&2, F.Finding, Twice.arm(pat, path)), Bool.pick(Nat,
    Laws.twice.same(twice.text(Twice.head(pat)), twice.text(Twice.head(Twice.tail(pat)))), 1n, 0n), Bool.pick(Nat,
    Laws.twice.same(Laws.twice.first(pat), Laws.twice.first(Laws.twice.after(pat))), 1n, 0n),
    twice.same(Twice.head(pat), Twice.head(Twice.tail(pat)), path),
    Equal.trans(Nat, Bool.pick(Nat, Laws.twice.same(twice.text(Twice.head(pat)),
      twice.text(Twice.head(Twice.tail(pat)))), 1n, 0n), Bool.pick(Nat, Laws.twice.same(Laws.twice.first(pat),
      twice.text(Twice.head(Twice.tail(pat)))), 1n, 0n), Bool.pick(Nat, Laws.twice.same(Laws.twice.first(pat),
      Laws.twice.first(Laws.twice.after(pat))), 1n, 0n),
      Equal.cong(Maybe<&2, String>, Nat, z => Bool.pick(Nat, Laws.twice.same(z,
        twice.text(Twice.head(Twice.tail(pat)))), 1n, 0n), twice.text(Twice.head(pat)), Laws.twice.first(pat),
        twice.head(pat)),
      Equal.cong(Maybe<&2, String>, Nat, z => Bool.pick(Nat, Laws.twice.same(Laws.twice.first(pat), z), 1n, 0n),
        twice.text(Twice.head(Twice.tail(pat))), Laws.twice.first(Laws.twice.after(pat)),
        Equal.trans(Maybe<&2, String>, twice.text(Twice.head(Twice.tail(pat))),
          twice.text(Twice.head(Laws.twice.after(pat))), Laws.twice.first(Laws.twice.after(pat)),
          Equal.cong(Tree.Node, Maybe<&2, String>, z => twice.text(Twice.head(z)), Twice.tail(pat),
            Laws.twice.after(pat),
            twice.tail(pat)),
          twice.head(Laws.twice.after(pat))))))

# a case statement onto the rest, its body and the rest both holding the law
law twice.case:
  for +kids: Tree.Node
  for +body: Tree.Node
  for +rest: Tree.Node
  for +path: String
  for ihb: {List.length(&2, F.Finding, Twice.walk(body, path)) == Laws.twice.cases(body) : Nat}
  for ihr: {List.length(&2, F.Finding, Twice.walk(rest, path)) == Laws.twice.cases(rest) : Nat}
  {List.length(&2, F.Finding, List.concat(&2, F.Finding, [Twice.arm(T.pattern(kids), path), Twice.walk(body, path),
      Twice.walk(rest, path)])) == Nat.add(Bool.pick(Nat, Laws.twice.dup(T.pattern(kids)), 1n, 0n),
      Nat.add(Laws.twice.cases(body), Laws.twice.cases(rest))) : Nat}

def twice.case(kids, body, rest, path, ihb, ihr):
  Equal.trans(Nat, List.length(&2, F.Finding, List.concat(&2, F.Finding, [Twice.arm(T.pattern(kids), path),
    Twice.walk(body, path), Twice.walk(rest, path)])), Nat.add(List.length(&2, F.Finding, Twice.arm(T.pattern(kids),
    path)), Nat.add(List.length(&2, F.Finding, Twice.walk(body, path)), List.length(&2, F.Finding, Twice.walk(rest,
    path)))),
    Nat.add(Bool.pick(Nat, Laws.twice.dup(T.pattern(kids)), 1n, 0n), Nat.add(Laws.twice.cases(body),
      Laws.twice.cases(rest))),
    M2.arms.cat(Twice.arm(T.pattern(kids), path), Twice.walk(body, path), Twice.walk(rest, path)),
    M2.arms.add3(List.length(&2, F.Finding, Twice.arm(T.pattern(kids), path)), Bool.pick(Nat,
      Laws.twice.dup(T.pattern(kids)), 1n, 0n), List.length(&2, F.Finding, Twice.walk(body, path)),
      Laws.twice.cases(body), List.length(&2, F.Finding, Twice.walk(rest, path)), Laws.twice.cases(rest),
      twice.arm(T.pattern(kids), path), ihb, ihr))

# any other statement onto the rest, its body and the rest both holding the law
law twice.stmt:
  for +body: Tree.Node
  for +rest: Tree.Node
  for +path: String
  for ihb: {List.length(&2, F.Finding, Twice.walk(body, path)) == Laws.twice.cases(body) : Nat}
  for ihr: {List.length(&2, F.Finding, Twice.walk(rest, path)) == Laws.twice.cases(rest) : Nat}
  {List.length(&2, F.Finding, List.append(&2, F.Finding, Twice.walk(body, path), Twice.walk(rest,
      path))) == Nat.add(Laws.twice.cases(body), Laws.twice.cases(rest)) : Nat}

def twice.stmt(body, rest, path, ihb, ihr):
  Equal.trans(Nat, List.length(&2, F.Finding, List.append(&2, F.Finding, Twice.walk(body, path), Twice.walk(rest,
    path))), Nat.add(List.length(&2, F.Finding, Twice.walk(body, path)), List.length(&2, F.Finding, Twice.walk(rest,
    path))), Nat.add(Laws.twice.cases(body), Laws.twice.cases(rest)),
    M2.esc.app(Twice.walk(body, path), Twice.walk(rest, path)),
    M2.esc.add(List.length(&2, F.Finding, Twice.walk(body, path)), Laws.twice.cases(body), List.length(&2, F.Finding,
      Twice.walk(rest, path)), Laws.twice.cases(rest), ihb, ihr))

# every case statement at any depth, each pattern read
law twice.walk:
  for nn: Tree.Node
  for +path: String
  {List.length(&2, F.Finding, Twice.walk(nn, path)) == Laws.twice.cases(nn) : Nat}

def twice.walk(nn, path):
  match nn:
    case Tree.Leaf{Lex.Tok{+k1429, +x1430, +l1431, +c1432}}:
      {==}
    case Tree.Group{+op1433, +ks1434, +cl1435}:
      {==}
    case Tree.Stmt{+sk1436, +sks1437, +sb1438}:
      {==}
    case Tree.NNil{}:
      {==}
    case Tree.NCons{+h1439, +t1440}:
      match h1439:
        case Tree.Leaf{Lex.Tok{+k1441, +x1442, +l1443, +c1444}}:
          twice.walk(t1440, path)
        case Tree.Group{+op1445, +ks1446, +cl1447}:
          twice.walk(t1440, path)
        case Tree.Stmt{+sk1448, +sks1449, +sb1450}:
          match sk1448:
            case Tree.SDef{}:
              twice.stmt(sb1450, t1440, path, twice.walk(sb1450, path), twice.walk(t1440, path))
            case Tree.SType{}:
              twice.stmt(sb1450, t1440, path, twice.walk(sb1450, path), twice.walk(t1440, path))
            case Tree.SLaw{}:
              twice.stmt(sb1450, t1440, path, twice.walk(sb1450, path), twice.walk(t1440, path))
            case Tree.SImport{}:
              twice.stmt(sb1450, t1440, path, twice.walk(sb1450, path), twice.walk(t1440, path))
            case Tree.SCase{}:
              twice.case(sks1449, sb1450, t1440, path, twice.walk(sb1450, path), twice.walk(t1440, path))
            case Tree.SFor{}:
              twice.stmt(sb1450, t1440, path, twice.walk(sb1450, path), twice.walk(t1440, path))
            case Tree.SLet{}:
              twice.stmt(sb1450, t1440, path, twice.walk(sb1450, path), twice.walk(t1440, path))
            case Tree.STerm{}:
              twice.stmt(sb1450, t1440, path, twice.walk(sb1450, path), twice.walk(t1440, path))
        case Tree.NNil{}:
          twice.walk(t1440, path)
        case Tree.NCons{+h1451, +t1452}:
          twice.walk(t1440, path)

# a def's cases, read when it calls itself
law twice.def:
  for mm: Maybe<&2, String>
  for +body: Tree.Node
  for +path: String
  {List.length(&2, F.Finding, Twice.check.def(mm, body, path)) == Laws.twice.def(mm, body) : Nat}

def twice.def(mm, body, path):
  match mm:
    case None{}:
      {==}
    case Some{+name}:
      Equal.trans(Nat, List.length(&2, F.Finding, Twice.check.def(Some{name}, body, path)), Bool.pick(Nat,
        Bool.not(Calls.calls(body, name)), 0n, Laws.twice.cases(body)),
        Bool.pick(Nat, Calls.calls(body, name), Laws.twice.cases(body), 0n),
        M2.param.stop(Bool.not(Calls.calls(body, name)), Twice.walk(body, path), Laws.twice.cases(body),
          twice.walk(body, path)),
        M2.arms.flip(Calls.calls(body, name), Laws.twice.cases(body)))

# the top-level defs, each read when it calls itself
law twice.go:
  for root: Tree.Node
  for +path: String
  {List.length(&2, F.Finding, Twice.check.go(root, path)) == Laws.twice_count(root) : Nat}

def twice.go(root, path):
  match root:
    case Tree.Leaf{Lex.Tok{+k1453, +x1454, +l1455, +c1456}}:
      {==}
    case Tree.Group{+op1457, +ks1458, +cl1459}:
      {==}
    case Tree.Stmt{+sk1460, +sks1461, +sb1462}:
      {==}
    case Tree.NNil{}:
      {==}
    case Tree.NCons{+h1463, +t1464}:
      match h1463:
        case Tree.Leaf{Lex.Tok{+k1465, +x1466, +l1467, +c1468}}:
          twice.go(t1464, path)
        case Tree.Group{+op1469, +ks1470, +cl1471}:
          twice.go(t1464, path)
        case Tree.Stmt{+sk1472, +sks1473, +sb1474}:
          match sk1472:
            case Tree.SDef{}:
              Equal.trans(Nat, List.length(&2, F.Finding, List.append(&2, F.Finding,
                Twice.check.def(Bind.declared(sks1473), sb1474, path), Twice.check.go(t1464, path))),
                Nat.add(List.length(&2, F.Finding, Twice.check.def(Bind.declared(sks1473), sb1474, path)),
                List.length(&2, F.Finding, Twice.check.go(t1464, path))),
                Nat.add(Laws.twice.def(Bind.declared(sks1473), sb1474), Laws.twice_count(t1464)),
                M2.esc.app(Twice.check.def(Bind.declared(sks1473), sb1474, path), Twice.check.go(t1464, path)),
                M2.esc.add(List.length(&2, F.Finding, Twice.check.def(Bind.declared(sks1473), sb1474, path)),
                  Laws.twice.def(Bind.declared(sks1473), sb1474), List.length(&2, F.Finding, Twice.check.go(t1464,
                  path)), Laws.twice_count(t1464), twice.def(Bind.declared(sks1473), sb1474, path), twice.go(t1464,
                  path)))
            case Tree.SType{}:
              twice.go(t1464, path)
            case Tree.SLaw{}:
              twice.go(t1464, path)
            case Tree.SImport{}:
              twice.go(t1464, path)
            case Tree.SCase{}:
              twice.go(t1464, path)
            case Tree.SFor{}:
              twice.go(t1464, path)
            case Tree.SLet{}:
              twice.go(t1464, path)
            case Tree.STerm{}:
              twice.go(t1464, path)
        case Tree.NNil{}:
          twice.go(t1464, path)
        case Tree.NCons{+h1475, +t1476}:
          twice.go(t1464, path)

def Laws.twice_counts(path, _text, _toks, tree, _bound, _items):
  twice.go(tree, path)
