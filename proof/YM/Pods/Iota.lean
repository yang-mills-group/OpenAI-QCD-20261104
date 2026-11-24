import YM.Pods.Factor
import YM.Pods.Gleams
import YM.Pods.Cove
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria
open Set Filter Function Finset Lattice Source
open scoped ContDiff Topology BigOperators Classical
namespace Hub
open QCD QCD.Lat UV Cylinder RG Wilson Grass MeasureTheory Cells QCD.RP
open Massive.Romance Massive.Chess
open Poised Plans Display Poised.Plans Stamp
open Massive.Patria.Depth TorusPCAC.Geometry
variable {c f m n:Side}{k d:ℕ}{F:ℕ}(T:Tiling n) -- n Side.change
variable (s:T.Cell)(i:Axis)
local notation "oP"=> T.copyMap
lemma point0 (x:Site n) : T.copyMap 0 x=x:=by
     funext i; have h : (T.omega 0).flip i=false:=by simp [Tiling.omega]
     have hp:= T.copy_formula (0:T.Cell) x i; rw [h, if_neg Bool.false_ne_true,T.starts_zero] at hp; exact sub_left_inj.mp hp -- sig
lemma chooseMap (s:T.Cell) (b:Cover) : ∃ (W:T.Cell→ Cover) (x:Site n), W s=b ∧ (∀ i,wrap n (W i)=oP i x):=by
    obtain ⟨x,h⟩:= T.pointed s (wrap n b); refine ⟨fun i=> if i=s then b else Lattice.lift (oP i x),x,if_pos rfl,fun i=>?_⟩; by_cases he:i=s; subst i; simp [h]; simp [he]
lemma relationG (W:T.Cell→ Cover)(x:Site n)(hp:∀ i,wrap n (W i)=oP i x): (∀ (p:T.Cell)(a:Axis)(v:T.Cell), wrap n (W (T.mate p a v))=(T.bandCut p a).reflect (wrap n (W v))):=by intro p a v; rw [hp,hp,T.after] -- sig .Area
variable (R:Regulator n 6)(hv:T.kind=.link)(hx:R.t=0)
local notation "Z₀"=> replicateR T R
open Chess.Fortuna
-- replica charges independent p pivot when actual X equals propagated.Seal constraints needed elsewhere but not this. ANY Bez.As.Sign.Ad.F path included.
include hx hv
lemma levy (X Y:Insertion n 6)(s v:T.Cell)(t:TapeWalk n T)(he:finish T s t=v)(h:Parity X)(hY:Parity Y)(hz: SignedEq (reels R.zeroCut (pathT T t) X) Y)(u:T.Cell):SignedEq (Z₀ X s u) (Z₀ Y v u):=by
    let k:= tag T v u; have hp:finish T s (k++t)=u:= by rw [app,he,tag_spec]
    apply SignedEq.trans ((along T R.zeroCut X (k++t) s u h hx hv hp).symm); have hB: pathT T (k++t)=pathT T k++pathT T t:=List.map_append; change SignedEq _ (reels R.zeroCut (pathT T k) Y); rw [hB,path_price]; rcases hz with h|h; rw [h]; exact Or.inr (by rw [h,path_neg]) -- parser `rw` refl consume.B
lemma due (X Y:Insertion n 6)(s v:T.Cell)(t:TapeWalk n T)(he: finish T s t=v)(h:Parity X)(hY:Parity Y)(hz: SignedEq (reels R.zeroCut (pathT T t) X) Y): floorL T R.average R X s=floorL T R.average R Y v:= by
    unfold floorL Chess.Fortuna.Array.rootL; apply congr_arg (fun x:ℝ=> x^((Fintype.card T.Cell:ℝ)⁻¹)); exact Chess.Fortuna.Array.holds_period R.average (signed_product _ _ _ (fun j=> levy T R hv hx X Y s v t he h hY hz j)) -- generalized signed_product only 6.B
end Hub
end YM.Massive.Patria
#print axioms YM.Massive.Patria.Hub.due
