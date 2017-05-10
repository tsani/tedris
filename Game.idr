module Game

import Data.Fin
import Data.Vect
import Data.ZZ

import NatToFin

%default total

namespace Misc
  data All : Vect n a -> (a -> Type) -> Type where
    ||| A collection of zero things vacuously all satisfy any property.
    Nil : All Nil p
    ||| If we know that some x satisfies a property and that a bunch of xs also
    ||| satisfy it, then of course the joint collection satisfies it too.
    (::) : p x -> All xs p -> All (x :: xs) p

  ||| Extract a witness from an All.
  index : {xs : Vect n a} -> Fin n -> All xs p -> (x : a ** p x)
  index f Nil = FinZElim f
  index FZ (prf :: prfs) = (_ ** prf)
  index (FS f) (_ :: prfs) = index f prfs

  DecAll : (prop : a -> Type) -> (xs : Vect n a) -> Type
  DecAll prop xs {n} =
    Either (i : Fin n ** Not (prop (index i xs))) (All xs prop)

  ||| Check a property for all elements of a vector.
  ||| Returns either a proof that all elements satisfy the property or a
  ||| counterexample.
  ||| @prop - the property to check
  ||| @f - a decision procedure for the property
  ||| @xs - the vector to verify
  decAll : {a : Type} ->
           {prop : a -> Type} ->
           (f : (x : a) -> Dec (prop x)) ->
           (xs : Vect n a) ->
           DecAll prop xs
  decAll _ Nil = Right Nil
  decAll dec (x::xs) =
    case dec x of
         Yes y => case decAll dec xs of
                       Left (i ** contra) => Left $ (FS i ** \pf => contra pf)
                       Right ys => Right (y :: ys)
         No contra => Left (FZ ** contra)

  ||| If 'n + k1 = m' and 'n + k2 = m', then 'k1 = k2'.
  plusInjectiveRight : {n : Nat} -> (n + k1 = m) -> (n + k2 = m) -> (k1 = k2)
  plusInjectiveRight {n=Z} Refl Refl = Refl
  plusInjectiveRight {n=S n} {m=Z} Refl q impossible
  plusInjectiveRight {n=S n} {m=Z} p Refl impossible
  plusInjectiveRight {n=S n} {m=S m} p q =
    let p' = succInjective _ _ p
        q' = succInjective _ _ q in
        plusInjectiveRight p' q'

  -- interface Bifunctor (f : Type -> Type -> Type) where
  --   map : (a -> b) -> (s -> t) -> f a s -> f b t

  -- Bifunctor Pair where
  --   map f g (x, y) = (f x, g y)

namespace Position
  namespace Point
    record Point where
      constructor MkPoint
      pointX : Nat
      pointY : Nat

    fst : Point -> Nat
    fst = pointX

    snd : Point -> Nat
    snd = pointY

  ||| A two-dimensional point bounded inside a rectangle at the origin.
  PointInBounds : (x : Nat) ->
                 (y : Nat) ->
                 (width : Nat) ->
                 (height : Nat) ->
                 Type
  PointInBounds x y w h = (LT x w, LT y h)

  BoundedPoint : (width : Nat) -> (height : Nat) -> Type
  BoundedPoint w h = (x : Nat ** y : Nat ** PointInBounds x y w h)

  ||| Extract the point from a BoundedPoint.
  getPoint : BoundedPoint w h -> Point
  getPoint (x ** y ** _) = MkPoint x y

  getX : BoundedPoint w h -> Nat
  getX = pointX . getPoint

  getY : BoundedPoint w h -> Nat
  getY = pointY . getPoint

  data IsPos : ZZ -> Type where
    ItIsPos : (n : Nat) -> IsPos (Pos n)

  ||| Decide whether an integer is positive.
  isPos : (z : ZZ) -> Dec (IsPos z)
  isPos (Pos n) = Yes (ItIsPos n)
  isPos (NegS n) = No (\ItIsPos impossible)

  UnboundedPoint : Type
  UnboundedPoint = (ZZ, ZZ)

  (+) : UnboundedPoint -> UnboundedPoint -> UnboundedPoint
  (a, b) + (x, y) = (a + x, b + y)

  ||| The result of a bounds-checking operation on a 2D rectangle.
  ||| Describes in what way the bounds-check fails, if any.
  data BoundsCheck2D : (w, h : Nat) -> UnboundedPoint -> Type where
    BoundsOk : LT x w -> LT y h -> BoundsCheck2D w h (Pos x, Pos y)
    XOOB : GTE x w -> LT y h -> BoundsCheck2D w h (Pos x, Pos y)
    YOOB : LT x w -> GTE y h -> BoundsCheck2D w h (Pos x, Pos y)
    XYOOB : GTE x w -> GTE y h -> BoundsCheck2D w h (Pos x, Pos y)
    XNeg : BoundsCheck2D w h (NegS x, Pos y)
    YNeg : BoundsCheck2D w h (Pos x, NegS y)
    XYNeg : BoundsCheck2D w h (NegS x, NegS y)

  data IsBoundsOk : BoundsCheck2D w h p -> Type where
    ItIsBoundsOk : IsBoundsOk (BoundsOk px py)

  data Cmp : Nat -> Nat -> Type where
    CmpLT : LT n m -> Cmp n m
    CmpEQ : Cmp n n
    CmpGT : GT n m -> Cmp n m

  cmpNat : (n : Nat) -> (m : Nat) -> Cmp n m
  cmpNat Z Z = CmpEQ
  cmpNat (S _) Z = CmpGT (LTESucc LTEZero)
  cmpNat Z (S _) = CmpLT (LTESucc LTEZero)
  cmpNat (S n) (S m) =
    case cmpNat n m of
         CmpLT lt => CmpLT (LTESucc lt)
         CmpEQ => CmpEQ
         CmpGT gt => CmpGT (LTESucc gt)

  checkBounds2D : (zz : UnboundedPoint) ->
                  (w, h : Nat) ->
                  BoundsCheck2D w h zz
  checkBounds2D (NegS _, NegS _) _ _ = XYNeg
  checkBounds2D (NegS _, Pos _) _ _ = XNeg
  checkBounds2D (Pos _, NegS _) _ _ = YNeg
  checkBounds2D (Pos x, Pos y) w h =
    case (cmpNat x w, cmpNat y h) of
         (CmpLT px, CmpLT py) => BoundsOk px py
         (CmpEQ, CmpLT py) => XOOB lteRefl py
         (CmpGT cx, CmpLT py) => XOOB (lteSuccLeft cx) py

         (CmpLT px, CmpEQ) => YOOB px lteRefl
         (CmpEQ, CmpEQ) => XYOOB lteRefl lteRefl
         (CmpGT cx, CmpEQ) => XYOOB (lteSuccLeft cx) lteRefl

         (CmpLT px, CmpGT cy) => YOOB px (lteSuccLeft cy)
         (CmpEQ, CmpGT cy) => XYOOB lteRefl (lteSuccLeft cy)
         (CmpGT cx, CmpGT cy) => XYOOB (lteSuccLeft cx) (lteSuccLeft cy)

  ||| Convert a positive integer to a natural.
  zz2nat : (z : ZZ ** IsPos z) -> Nat
  zz2nat (Pos n ** ItIsPos n) = n

  ||| Convert a natural to a positive integer.
  nat2zz : (n : Nat) -> (z : ZZ ** IsPos z)
  nat2zz n = (Pos n ** ItIsPos n)

  ||| Conversion from positive integer to natural and back is a no-op.
  z2n2z : (e : (z : ZZ ** IsPos z)) -> (nat2zz (zz2nat e) = e)
  z2n2z (Pos _ ** ItIsPos _) = Refl

  ||| An integer can be converted to a Fin it it is positive and bounded.
  zzToFin : (e : (z : ZZ ** IsPos z)) -> LTE (zz2nat e) m -> Fin (S m)
  zzToFin (Pos _ ** ItIsPos Z) LTEZero = FZ
  zzToFin (Pos _ ** ItIsPos (S n)) (LTESucc p) =
    let ih = zzToFin (nat2zz n) p in
        FS ih

namespace Offset
  ||| An offset is just an integer.
  Offset : Type
  Offset = ZZ

  ||| A proof that a particular integer is a valid offset for a point in a
  ||| one-dimensional discrete interval.
  ||| The point is represented by a bounds-proof.
  |||
  ||| @n - the point
  ||| @m - its bound
  ||| @z - the valid offset
  data ValidOffset : LT n m -> (z : Offset) -> Type where
    ||| A positive offset is valid if there's enough room.
    Positive : {p : LT n m} ->
               LT (o + n) m ->
               ValidOffset p (Pos o)

    ||| A negative offset is valid if it is small enough.
    ||| Remark: we check a strict less-than for the offset and the point
    ||| because o=Z means that we're subtracting by *one* !
    Negative : {p : LT n m} -> LT o n -> ValidOffset p (NegS o)

  ||| Decides whether a given offset is valid for a given point.
  checkOffset : (p : LT x w) -> (o : Offset) -> Dec (ValidOffset p o)
  checkOffset LTEZero _ impossible
  checkOffset (LTESucc p) {w=Z} _ impossible
  checkOffset p {x} {w=S w} (Pos o) =
    case isLTE (S (o + x)) (S w) of
         Yes q => Yes (Positive q)
         No contra => No $ \offset =>
                     case offset of
                          Positive q => absurd (contra q)
                          Negative _ impossible
  checkOffset p {x} {w=S w} (NegS o) =
    case isLTE (S o) x of
         Yes q => Yes (Negative q)
         No contra => No $ \offset =>
                     case offset of
                          Positive _ impossible
                          Negative q => absurd (contra q)

namespace Offset2D
  Offset2D : Type
  Offset2D = (ZZ, ZZ)

  ||| Reflects the point along the x-axis and the y-axis.
  negate : Offset2D -> Offset2D
  negate (x, y) = (-x, -y)

  doubleNegateElim : (p : Offset2D) -> (-(-p) = p)
  doubleNegateElim (x, y) =
    rewrite doubleNegElim x in rewrite doubleNegElim y in Refl

  ||| A proof that a particular vector is a valid offset for a point in a
  ||| two-dimensional grid.
  ||| A vector is a valid offset if each component is a valid offset.
  data ValidOffset2D : PointInBounds x y w h -> Offset2D -> Type where
    MkValidOffset2D : ValidOffset xp xo ->
                      ValidOffset yp yo ->
                      ValidOffset2D (xp, yp) (xo, yo)

  ||| The result of checking an offset, which describes in what way the offset
  ||| is invalid, if it is.
  data OffsetCheck2D : PointInBounds x y w h -> Offset2D -> Type where
    OffsetOk : ValidOffset2D p o -> OffsetCheck2D p o

    VerticalOOB : ValidOffset px ox ->
                  Not (ValidOffset py oy) ->
                  OffsetCheck2D (px, py) (ox, oy)

    HorizontalOOB : Not (ValidOffset px ox) ->
                    ValidOffset py oy ->
                    OffsetCheck2D (px, py) (ox, oy)

    BothOOB : Not (ValidOffset px ox) ->
              Not (ValidOffset py oy) ->
              OffsetCheck2D (px, py) (ox, oy)

  ||| Checks whether a point, guaranteed to lie within some bounds, is
  ||| validly offset by a given offset.
  checkOffset2D : (p : PointInBounds x y w h) ->
                  (o : Offset2D) ->
                  OffsetCheck2D p o
  checkOffset2D (px, py) (ox, oy) =
    case (checkOffset px ox, checkOffset py oy) of
         (Yes qx, Yes qy) => OffsetOk (MkValidOffset2D qx qy)
         (Yes qx, No cy) => VerticalOOB qx cy
         (No cx, Yes qy) => HorizontalOOB cx qy
         (No cx, No cy) => BothOOB cx cy

  ||| A predicate claiming that a bounds check was successful.
  data IsOffsetOk : OffsetCheck2D p o -> Type where
    ItIsOffsetOk : IsOffsetOk (OffsetOk v)

  ||| A predicate claiming that a bounds check was unsuccessful.
  data IsOffsetNotOk : OffsetCheck2D p o -> Type where
    NotOkVertical : IsOffsetNotOk (VerticalOOB vx cy)
    NotOkHorizontal : IsOffsetNotOk (HorizontalOOB cx vy)
    NotOkBoth : IsOffsetNotOk (BothOOB cx cy)

namespace Grid
  data Grid : (width : Nat) -> (height : Nat) -> (tileType : Type) -> Type where
    MkGrid : Vect width (Vect height tileType) -> Grid width height tileType

  ||| Construct a grid of any size by filling it with a particular value.
  replicate : (w, h : Nat) -> (x : a) -> Grid w h a
  replicate w h x = MkGrid (replicate w (replicate h x))

  ||| Apply a function to a particular element of a vector.
  modify : (a -> a) -> Fin n -> Vect n a -> Vect n a
  modify _ i Nil = FinZElim i
  modify f FZ (x :: xs) = f x :: xs
  modify f (FS i) (x :: xs) = x :: modify f i xs

  ||| Apply a function to a particular element of a grid.
  modify2D : (a -> a) -> Fin w -> Fin h -> Grid w h a -> Grid w h a
  modify2D f ix iy (MkGrid cols) = MkGrid (modify (modify f iy) ix cols)

  ||| Extract a particular element from the grid.
  index : BoundedPoint w h -> Grid w h a -> a
  index (x ** y ** (px, py)) (MkGrid g) =
    let col = index (nat2FinLT (x ** px)) g in
        index (nat2FinLT (y ** py)) col

namespace Tile
  ||| A position on the grid can be either full or empty.
  ||| Eventually, we might want to track *when* the block was placed there.
  data Tile : Type where
    Empty : Tile
    Full : Tile

  ||| A predicate claiming that a tile is empty.
  data IsEmpty : Tile -> Type where
    ItIsEmpty : IsEmpty Empty

  ||| A predicate claiming that a tile is full.
  data IsFull : Tile -> Type where
    ItIsFull : IsFull Full

  ||| We usually deal with a tile grid, in which is simply a grid containing
  ||| tiles.
  TileGrid : (width : Nat) -> (height : Nat) -> Type
  TileGrid w h = Grid w h Tile

namespace Piece
  ||| A piece is bunch of blocks, simply represented by their coordinates.
  ||| size of a piece is the number of blocks in it. In Tetris is this always
  ||| 4.
  record PieceBody (size : Nat) where
    constructor MkPiece
    blocks : Vect size Offset2D

  ||| Get the absolute coordinates of every block in a piece.
  absolutePiece : UnboundedPoint -> PieceBody n -> Vect n UnboundedPoint
  absolutePiece (xo, yo) (MkPiece blocks) = map off blocks where
    off (x, y) = (xo + x, yo + y)

namespace Rotation
  data Rotation = CW | CCW

  rotate : Rotation -> PieceBody n -> PieceBody n
  rotate CW = rotateCW where
    rotateCW : PieceBody n -> PieceBody n
    rotateCW (MkPiece blocks) = MkPiece (map r blocks) where
      r : Offset2D -> Offset2D
      r (x, y) = (y, -x)
  rotate CCW = rotateCCW where
    rotateCCW : PieceBody n -> PieceBody n
    rotateCCW (MkPiece blocks) = MkPiece (map r blocks) where
      r : Offset2D -> Offset2D
      r (x, y) = (-y, x)

namespace Game
  ||| Configuration of the game, which is held constant throughout the
  ||| execution.
  record GameSettings where
    constructor MkGameSettings
    pieceSize : Nat -- size of a piece; this is 4 in tetris
    width : Nat -- width of the board
    height : Nat -- height of the board
    spawnPoint : Nat -- the x coordinate where new pieces spawn

  ||| The current overall state of the game.
  ||| In tetris, you either play, or you lose. There is no win.
  data Outcome = Playing | Lost

  ||| An absolute point is valid if:
  |||   * its coordinates are positive
  |||   * its coordinates boundscheck
  |||   * the tile on the grid identified by it is empty
  data AbsolutePointIsOk : TileGrid w h ->
                           UnboundedPoint ->
                           Type where
    MkAbsolutePointIsOk : (px : LT x w) -> -- the point is in the x bounds
                          (py : LT y h) -> -- the point is in the y bounds
                          IsEmpty (index (x ** y ** (px, py)) grid) ->
                          AbsolutePointIsOk grid (Pos x, Pos y)

  ||| An absolute point is invalid if:
  |||   * its coordinates are positive
  |||   * its coordinates boundscheck
  |||   * but, the tile on the grid identified by it is full
  data AbsolutePointIsInvalid : TileGrid w h ->
                                UnboundedPoint ->
                                Type where
    MkAbsolutePointIsInvalid : (px : LT x w) ->
                               (py : LT y h) ->
                               IsFull (index (x ** y ** (px, py)) grid) ->
                               AbsolutePointIsInvalid grid (Pos x, Pos y)

  ||| The current piece that the playing controls can be in several states.
  ||| The piece changes between this states as follows.
  |||   * when a piece is simply floating on the board, it must be valid.
  |||   * when a piece overlaps with full tiles in the board, it is invalid.
  |||   * when descending a piece would cause it to become invalid, the piece
  |||     freezes, and the well is extended; the piece becomes NoPiece.
  |||   * when there is no piece, a hypothetical new piece is looked at:
  |||     when that piece would be valid, then the game continues
  |||     when that piece would be invalid, the game proceeds to GameOver.
  ||| @center - the position of the piece's center point.
  ||| @size - the size of the piece.
  ||| @grid - the grid in which validity is checked.
  data GamePiece : (center : UnboundedPoint) ->
                   (size : Nat) ->
                   (grid : TileGrid w h) ->
                   Type where
    NoPiece : GamePiece center size grid

    ValidPiece : (center : UnboundedPoint) ->
                 (body : PieceBody size) ->
                 (grid : TileGrid w h) ->
                 All (absolutePiece center body) (AbsolutePointIsOk grid) ->
                 GamePiece center size grid

    InvalidPiece : (center : UnboundedPoint) ->
                   (body : PieceBody size) ->
                   (grid : TileGrid w h) ->
                   (f : Fin size) ->
                   let zz = index f (absolutePiece center body) in
                   AbsolutePointIsInvalid grid zz ->
                   GamePiece center size grid

  ||| Extend a grid by adding all the points of a piece to it.
  extend : (grid : TileGrid w h) ->
           (center : UnboundedPoint) ->
           (body : PieceBody size) ->
           (prfs : All (absolutePiece center body) (AbsolutePointIsOk grid)) ->
           TileGrid w h
  extend grid center body prfs = go grid (absolutePiece center body) prfs where
    go : (grid : TileGrid w h) ->
         (xs : Vect size UnboundedPoint) ->
         All xs (AbsolutePointIsOk grid) ->
         TileGrid w h
    go g Nil Nil = g
    -- why does idris need me to explicitly show the following case is
    -- impossible?
    go g ((NegS x, NegS y) :: xs) (MkAbsolutePointIsOk _ _ _ :: prfs) impossible
    go g ((Pos x, Pos y) :: xs) (MkAbsolutePointIsOk px py _ :: prfs) =
      let ix = nat2FinLT (x ** px) in
      let iy = nat2FinLT (y ** py) in
        modify2D (const Full) ix iy (go g xs prfs)

  ||| A point is at the bottom of the well if its y-coordinate's successor is
  ||| the height of the well.
  PointAtBottom : (point : UnboundedPoint) -> (h : Nat) -> Type
  PointAtBottom (_, Pos y) h = (S y = h)
  PointAtBottom (_, NegS _) _ = Void

  ||| A piece is at the bottom if one of its points is at the bottom.
  PieceAtBottom : (center : UnboundedPoint) ->
                  (body : PieceBody size) ->
                  (h : Nat) ->
                  Type
  PieceAtBottom center body h {size} =
    (f : Fin size ** PointAtBottom (index f (absolutePiece center body)) h)

  ||| A point overlaps the grid if it boundschecks and the tile on the grid
  ||| identified by it is full.
  PointOverlap : UnboundedPoint -> TileGrid w h -> Type
  PointOverlap (NegS _, _) _ = Void
  PointOverlap (_, NegS _) _ = Void
  PointOverlap (Pos x, Pos y) grid {w} {h} =
    (px : LT x w ** py : LT y h ** IsFull (index (x ** y ** (px, py)) grid))

  ||| A piece overlaps the grid if one of the points overlaps the grid.
  PieceOverlap : (center : UnboundedPoint) ->
                 (body : PieceBody size) ->
                 (grid : TileGrid w h) ->
                 Type
  PieceOverlap center body grid {size} =
    (f : Fin size ** PointOverlap (index f (absolutePiece center body)) grid)

  ||| A piece is valid if all its points are valid.
  PieceIsOk : (center : UnboundedPoint) ->
              (body : PieceBody size) ->
              (grid : TileGrid w h) ->
              Type
  PieceIsOk center body grid =
    All (absolutePiece center body) (AbsolutePointIsOk grid)

  ||| The transition system of the game.
  ||| @s - the configuration of the game.
  ||| @grid - the current contents of the grid.
  ||| @piece - the current piece the user controls
  ||| @pieces - an infinite stream of new piece shapes to use.
  ||| @outcome - whether the game has been lost yet.
  data Game : (s : GameSettings) ->
              (grid : TileGrid (width s) (height s)) ->
              (piece : GamePiece center (pieceSize s) grid) ->
              (pieces : Stream (PieceBody (pieceSize s))) ->
              (outcome : Outcome) ->
              Type where
    InitialGame : (s : GameSettings) ->
                  (pieces : Stream (PieceBody (pieceSize s))) ->
                  let grid = replicate (width s) (height s) Empty in
                  Game s grid NoPiece pieces Playing

    ||| If we have a grid with no piece in it,
    ||| then we pump the stream for a new piece,
    NewPiece : let center = (Pos (spawnPoint s), 0) in
               (prf : PieceIsOk center body grid) ->
               let newPiece = ValidPiece center body grid prf in
               Game s grid NoPiece (body::pieces) Playing ->
               Game s grid newPiece pieces Playing

    GameOver : (f : Fin (pieceSize s)) ->
               let center = (Pos (spawnPoint s), 0) in
               let zz = index f (absolutePiece center body) in
               (prf : AbsolutePointIsInvalid grid zz) ->
               let piece = InvalidPiece center body grid f prf in
               Game s grid NoPiece (body::pieces) Playing ->
               Game s grid piece pieces Lost


    ||| You can descend the piece by one provided that after the move, the
    ||| piece bounds-checks and produces no grid-overlap
    Descend : let newCenter = (0, 1) + center in
              let abs = absolutePiece newCenter body in
              (prf' : PieceIsOk newCenter body grid) ->
              let piece = ValidPiece center body grid prf in
              let newPiece = ValidPiece newCenter body grid prf' in
              Game s grid piece pieces Playing ->
              Game s grid newPiece pieces Playing

    ||| You can rotate a piece provided that the rotation produces a valid
    ||| piece.
    Rotate : (r : Rotation) ->
             let newBody = rotate r body in
             (prf' : PieceIsOk center newBody grid) ->
             let piece = ValidPiece center body grid prf in
             let newPiece = ValidPiece center newBody grid prf' in
             Game s grid piece pieces Playing ->
             Game s grid newPiece pieces Playing

    ||| A piece freezes when it is at the bottom of the well or when
    ||| descending would produce grid-overlap.
    ||| The freezing action adds the points of the piece to the grid.
    Freeze : let piece = ValidPiece center body grid prfs in
             Either
               (PieceAtBottom center body h)
               (PieceOverlap ((0, 1) + center) body grid) ->
             Game s grid piece pieces Playing ->
             Game s (extend grid center body prfs) NoPiece pieces Playing
