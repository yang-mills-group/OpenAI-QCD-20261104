import YM.Pods.Iota
/-! Interpolate any off-centered register. req rooted bracket only. Same grading. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria
open Set Filter Function Finset Lattice Source
open scoped ContDiff Topology BigOperators Classical
namespace Hub
open QCD QCD.Lat UV Cylinder RG Wilson Grass MeasureTheory Cells QCD.RP
open Massive.Romance Massive.Chess Chess.Fortuna
open Poised Plans Display Poised.Plans Stamp
open Massive.Patria.Depth TorusPCAC.Geometry
variable {c f m n:Side}{k d:ℕ}{F:ℕ}(T:Tiling n) (s:T.Cell)(i:Axis)
-- centered 0. all cover.Interp.V cost input h.A. BP
variable (R:Regulator n 6)(V:Bore d)(sym:RawSym)(hz:Rubric sym V)(hv:T.kind=.link)(hx:R.t=0) (w:Label d)(q:Bool)(hu:moored w.val q)
variable (he:0 ≤ R.β)(hn:4 ≤ n.val)
local notation "Q" b:arg => V n b w
local notation "Δ"=> (step i : Cover)
local notation "Fχ"=> floorL T R.average R
local notation "Ψ" j:arg => T.copyMap j
local notation "θ"=> T.omega
local notation "Lv"=> replicateR T R
local notation "μ"=> R.average
local notation "O"=> (0:T.Cell)
-- exhibition.Stat.Check transformations.
lemma safety (i:Axis)(v:T.Cell): ((T.omega v).act (step i : Site n))= if (T.omega v).flip i then - step i else step i:=by
   ext1 k; rw [show (T.omega v).act (step i : Site n) k = _ from Signed.act_at (T.omega v) _ k]; split_ifs with H I <;> by_cases he:k=i <;> simp_all -- v.P.
lemma esc (i:Axis)(v:T.Cell): (T.omega v).act (step i:Cover)=if (T.omega v).flip i then -step i else step i:=by
   ext1 s; rw [show (T.omega v).act (step i:Cover) s=_ from Signed.act_at (T.omega v) _ s]; split_ifs with H I <;> by_cases he:i=s <;> simp_all <;> simp [Ne.symm he]
include hv hx hu hz
lemma usesP (p:T.Cell)(W:T.Cell→ Cover)(x:Site n)(hp:∀ i,wrap n (W i)=T.copyMap i x)(L:TapeWalk n T)(v:T.Cell)(he:finish T p L=v) : SignedEq (Lv (Q (W p)) p v) (V n (W v) (spine sym w (axes (pathT T L)))):=by -- Z₁→Q
    apply ((along T R.zeroCut (Q (W p)) L p v ⟨q,fade V sym hz w q hu _⟩ hx hv he).symm).trans; have hm:= (spirals R V sym hz w q hu T p hv W (relationG T W x hp) hx L).2; exact he ▸ hm
-- step. X0 center.Cell.Pos.Root.In translated product. Using path formula pick Wm.C lengths.Safe on all. S shifted.De.Bit.Pick.W_i for every shape.V.Trans.RelationG requires shifted Root lifts.W.W.F for replicating REFLECTION moves. Construct each W explicitly lifted from affine.P.Canonical.
variable (b:Cover)
local notation "b⁻"=>b- Δ
include he hn
lemma rocking (hF:Base T 0 0 (Q (b- Δ)))(hG:Base T 0 0 (Q (b+Δ))) : Fχ (V n b w) O ^2 ≤ Fχ (V n (b-Δ) w) O*Fχ (V n (b+Δ) w) O:=by
   obtain ⟨W,x,hW,h₀⟩:= chooseMap T O b
   let f(v:T.Cell):= if (T.omega v).flip i then -Δ else Δ
   let P(v:T.Cell):= b+f v
   let F(v:T.Cell):= Q (P v) -- rename
   have hP(v:T.Cell):Base T 0 0 (F v):=by unfold F P f; split_ifs; exact sub_eq_add_neg b Δ ▸ hF; exact hG
   let B:= figure T R hv (fun _ : T.Cell=> (0:T.Cell)) F hP hx
   let Y:= fun v : T.Cell=> Lv (F v) O v
   choose L ht using (connect (T:=T) O) -- signature
   let α(v:T.Cell):= spine sym w (axes (pathT T (L v))); let A(v:T.Cell):= V n (W v) (α v); let D(v:T.Cell):= V n (W v+Δ) (α v)
   have h(v):SignedEq (Lv (Q b) O v) (A v):= hW ▸ usesP T R V sym hz hv hx w q hu _ W x h₀ (L v) v (ht v)
   have hY(v):SignedEq (Y v) (D v):=by
       let b' := x+wrap n (f v); let ℓ(u:T.Cell):= W u+(T.omega u).act (f v)
       have hxv : ∀ u: T.Cell,wrap n (ℓ u)= T.copyMap u b':=by
           intro j; unfold ℓ; rw [map_add,← Lattice.wrap_signed,h₀]; unfold Tiling.copyMap affine b'; rw [Signed.act_add]; abel -- signature wrap
       have hψ:= usesP T R V sym hz hv hx w q hu O ℓ b' hxv (L v) v (ht v)
       have hL: ℓ 0=P v:=by
           have hg:T.omega O=1:= Signed.ext rfl (funext (fun i=>by simp [Cells.Tiling.omega])); unfold ℓ P; rw [hg,Signed.act_one,hW]
       let hxT:= fun i v=> esc T i v
       have hr : ℓ v=W v+Δ:=by
           unfold ℓ f; split_ifs with hP
           · rw [Signed.act_neg,hxT i v,if_pos hP,neg_neg]
           rw [hxT i v,if_neg hP]
       rw [hL,hr] at hψ; exact hψ
   let l:= (univ:Finset T.Cell).toList
   have hE: ‖R.average ((l.map Y).prod)‖= Fχ (Q b) O^Fintype.card T.Cell:=by
         rw [roof_power]; have hxB:(l.map (Lv (Q b) O)) =l.map (Lv (Q b) O):=rfl -- filler
         change ‖R.average ((l.map Y).prod)‖= ‖R.average ((l.map (Lv (Q b) O)).prod)‖; rw [Chess.Fortuna.Array.holds_period R.average (signed_product l _ _ hY), Chess.Fortuna.Array.holds_period R.average (signed_product l _ _ h), ferry_many R _ hx Δ A D (fun i=> hz.advances ..)] -- arguments
   let W(v:T.Cell):= Fχ (F v) O
   have hc:Fχ (Q b) O^Fintype.card T.Cell ≤ ∏ i:T.Cell,W i:= hE ▸ (Fortuna.Array.operation id B μ (averageSeal T R hv he hn 0))
   let Q':= V n (b-Δ) w; let Q'':= V n (b+Δ) w; let ξ:= Fχ Q' O * Fχ Q'' O
   let t:= Equiv.ofBijective (T.mate 0 i) (Function.Involutive.bijective (T.mate_invol 0 i)); have ht(i'): (T.omega (t i')).flip i = !(T.omega i').flip i := T.flip_here 0 i i'
   have hf : (∏ z:T.Cell,W z)^2=ξ^(Fintype.card T.Cell):=calc
    _ = (∏ z:T.Cell,W z) * ∏ j:T.Cell,W (t j) := by rw [pow_two, Equiv.prod_comp]
    _ = ∏ j:T.Cell, ξ := by
      rw [← Finset.prod_mul_distrib]; apply Finset.prod_congr rfl; intro v _
      unfold W F P f ξ Q' Q''; cases H:(T.omega v).flip i <;> simp only [ht,H, Bool.not_false,Bool.not_true,Bool.false_eq_true, ↓reduceIte,← sub_eq_add_neg]; rw [mul_comm] -- simp under.C
    _ = _ := by simp
   apply le_of_pow_le_pow_left₀ T.cells_positive.ne' (mul_nonneg (floor_nn ..) (floor_nn ..)); rw [← pow_mul,pow_mul']; exact ((pow_le_pow_left₀ (pow_nonneg (floor_nn ..) _) hc 2).trans_eq hf) -- `rw` cast ξ? after first, `pow_mul'` expands both sides.T check
end Hub
end YM.Massive.Patria
#print axioms YM.Massive.Patria.Hub.rocking
