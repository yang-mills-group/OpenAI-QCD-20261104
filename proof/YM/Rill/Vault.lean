import YM.Rill.Grove
/-! Honest hierarchy at all engineering horizons.
Passing to actual subsequence with the same payments C, not mesh-by-mesh. Full Euclidean
rotation action is not included here (requires e.g. torque & Stress).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tarn
open YM.Fir Fir Set Function Filter
open UV Patria Patria.Depth Patria.Hub Needle Poised Poised.Plans Poised.Plans.Stamp
open Choir Choir.Strip HarmonyF Quilt
open scoped Topology ContDiff BigOperators Classical ComplexOrder
variable {C:Sequence}{P:Calibration C}{K:Choir}{φ:ℕ→ℕ}
noncomputable abbrev lampU (P:Calibration C)(K:Choir):K.W:= K.focus none 0 (P.sym.unit 0)
-- Before lie. Use provisional terms for Consumers. Sup spectral.
structure Foil (P:Calibration C)(K:Choir)(T:Pollens P K):Prop where
    empty: K.total 0 0 0=1
    unit(d:ℕ)(v:Averaging):K.focus v d (P.sym.unit d)=lampU P K
    functor(n:ℕ)(x:Points (n+1))(hx:x∈conf (n+1))(z:Fin n→ K.W): K.total _ x (Fin.cons (lampU P K) z)= K.total n (Points.tail x) z
    translation (n:ℕ)(x:Points n)(hx:x∈conf n)(z:E4)(u):K.total n (Points.across z x) u=K.total n x u
    discrete (n:ℕ)(x:Points n)(hx:x∈conf n)(p:EuPin)(s:Signed)(he:p.Lifts s)(u): K.total n (Points.move p.coord x) (T.spin p ∘u)=K.total n x u
    starry (l:Strip K)(hl:Strip.distinct l)(a:Axis): Strip.tone (oppositeS T a l)=star (Strip.tone l)
    charge (n:ℕ)(x:Points n)(hx:x∈conf n)(u): K.total n x (T.charge ∘ u)=K.total n x u
    parity (n:ℕ)(x:Points n)(hx:x∈conf n)(u): K.total n x (T.parity ∘ u)=K.total n x u
    flavor (n:ℕ)(x:Points n)(hx:x∈conf n)(p:FlavorTorus)(u):K.total n x (T.flavor p ∘ u)=K.total n x u
    flips(l v:Strip K)(x y:E4 ×K.W)(p q: Bool)(h:distinct (l++ x::y::v))(hx:markedW T p x.2)(hy:markedW T q y.2): tone (l ++ x::y::v) = (if p && q then -1 else 1)*tone (l ++y::x::v)
    priests (a:Axis)(n:ℕ)(v:Fin n→Strip K)(hx:∀ i,Sunny (v i) a)(w:Fin n→ℂ):0 ≤ crestG T a n v w
    vigor(a:Axis): marvel T a
    realPair (a:Axis)(v:K.W)(hx:v≠0):∃ r:ℝ,0<r ∧ 0<K.total 2 (points ![0,r • basis a]) ![T.adj a v,v]
variable {β e:ℝ}(hp:C.Path β e) (h:P.System) (H:K.Harmony P φ) (hv:Tendsto φ atTop atTop)
variable (G:∀ d,Cottage P d)(hx:Sway C.S)
include hp h H hv G hx
lemma bow (T:Pollens P K): Foil P K T where
    empty:=HarmonyF.empty hp H hv
    unit d v:= common_unit hp H hv h T d 0 v none
    functor n x hu z:= sparks hp H hv h x hu z none 0
    translation n x hx z v:= carried hp H hv h _ hx _ _
    discrete n x hx p s he v:= wetSpin hp H hv h T x hx v _ _ he
    starry l hl a:=console h hv T l _ hp H hl
    charge n x hx v:=candlesCharge hp H hv h T x hx v
    parity n x hx v:=candlesParity hp H hv h T x hx v
    flavor n x hx v z:= candlesFlavor hp H hv h T x hx z v
    flips l v x y p q he hq hh:= Choir.Harmony.swapS hp H hv h T l v x y p q he hq hh
    priests a n v hv' w:= Choir.rpTrue h hv T a hp G hx H v hv' w
    vigor a:= skill T a G hx hp H hv h
    realPair a v ht:= faithfulW h hv T a hp G hx H v ht
omit H
lemma successF:∃ g:ℕ→ℕ,StrictMono g∧∃ (Q:Choir)(T:Pollens P Q), Q.Harmony P (φ ∘g) ∧Foil P Q T:=by
    obtain ⟨g,hg,Q,hQ⟩:= Choir.angels (G:=G) hp hx hv; obtain ⟨T⟩:= owned h hp hQ (hv.comp hg.tendsto_atTop); exact ⟨g,hg,Q,T,hQ,bow hp h hQ (hv.comp hg.tendsto_atTop) G hx T⟩
end YM.Massive.Tarn
#print axioms YM.Massive.Tarn.successF
