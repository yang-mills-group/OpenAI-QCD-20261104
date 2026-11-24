import YM.Shade.Belt
import YM.Shade.Ozone
import YM.Tarn.Spoil
import YM.Alum.Chord
/-!
   Exact anchored penny stacks for central matched-PC layer.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Needle
open Filter Set Metric
open Lattice Cells QCD QCD.Lat UV Lattice Needle Patria Patria.Depth Patria.Hub Poised Plans Plans.Stamp Intag Intag.CardsT Intag.Vale GaugeP Rolls
open scoped Topology ContDiff BigOperators Classical
variable {C:Sequence} {k i j ℓ n:ℕ}{X:Type} [AddCommGroup X][Module ℝ X]

open Function Intag Intag.CardsT
variable {β ε:ℝ}(hp:C.Path β ε)(x:E4)(u:Averaging)
set_option quotPrecheck false
local notation "p★"=> bead (C.S.spacing j) x
local notation "V" i:arg=> C.S.side (C.R i) (C.N i)
include hp
lemma windowV (j:ℕ)(hh:2*C.S.spacing j< ‖x‖): ∀ᶠ i:ℕ in atTop, wrap (C.S.side (C.R i) j) (bead (C.S.spacing j) x) ≠ 0:=by
       let p:=bead (C.S.spacing j) x; let v:=digit (C.S.spacing j) p; have hv:0< dist 0 v:=dist_pos.mpr fun h=>by have hp:=smoothV (space0 C.S j) x; change dist v x≤_ at hp; rw [← h, dist_zero_left] at hp; exact hh.not_ge hp
       filter_upwards [hp.uv.tendsto_atTop.eventually_ge_atTop j, fullPrice hp (dist 0 v) (dist 0 v)] with i hi he hQ
       let k:= ratioTo C.S (C.N i) j; have hg: digit (C.S.spacing (C.N i)) (k • p)=v:= (gears hi p).symm -- sig
       specialize he 0 (k • p); rw [map_zero,digit_zero,hg,show wrap _ (k • p)=(0:Site (V i)) from ?_, Lattice.separation_self] at he; simp only [Nat.cast_zero,mul_zero] at he; exact not_le_of_gt (half_pos hv) (he le_rfl le_rfl)
       let g:=viewW C.S (C.R i) hi; change wrap _ (g.count.val • p)=_; rw [← Ratio.embed_wrap g,hQ]; simp [Ratio.embed]
-- hJ needed. s time.R.
variable (hj:j≤ℓ)(hX:ℓ≤C.N i)(hW:j+1 ≤ C.N i)
include hj hX hW
lemma aloft (r:stalk C i)(X:stalk C i)(A B:ℝ)(hG: GreenP C i j r A)(hQ: Knoll C i j ℓ X u B) (h:6≤(C.S.step j).L.val)(he:(wrap (C.S.side (C.R i) j) (bead (C.S.spacing j) x))≠0):‖rod2 C i r (checkedT u (ratioTo C.S (C.N i) ℓ) X (penC C.S j ℓ x))‖ ≤ A*B:=by
       let y:=penC C.S j ℓ x; let V':= checkedT u (ratioTo C.S (C.N i) ℓ) X y; let B':= C.R i; let W:=(C.A i).regulator; let E:= C.S.side B' ℓ; let S:= wrap (C.S.side B' j) p★; let T:= Column.sky C.S B' j (C.N i) (hj.trans hX) (evenW C.S B' (hp.even i) j) (0:Site E); let P: Fin 2→T.Cell:=![0,S]
       have hs: Injective P:=by intro i j h; fin_cases i <;> fin_cases j <;> first|rfl|exact False.elim (he h)|exact False.elim (he h.symm)
       let F: Fin 2→Insertion (V i) 6:=![r 0,V']; let w':Fin 2→ℝ:=![A,B]; have hh: Gold W T (P 0) (F 0) (w' 0):= hG hW T rfl rfl _ 0 (by rw [map_zero]; exact GaugeP.lawn i j ℓ hj (hp.even i) hX hW h)
       have hm: Gold W T (P 1) (F 1) (w' 1):= hQ hj hX (hp.even i) 0 S y (GaugeP.joinsC (viewW C.S B' hj) (evenW C.S _ (hp.even i) j) p★ (viewOdd ..))
       have hz:= Gold.value P hs F w' (Fin.forall_fin_two.mpr ⟨hh,hm⟩) rfl rfl ((hp.normalized i).beta_pos (Nat.le_refl _) |>.le) (sideW hp i _) (engaged hp i)
       simp only [List.ofFn_succ,List.ofFn_zero,List.prod_nil,List.prod_cons,mul_one,Fin.prod_univ_succ,Finset.univ_eq_empty,Finset.prod_empty] at hz; exact hz
end YM.Massive.Needle
#print axioms YM.Massive.Needle.windowV
#print axioms YM.Massive.Needle.aloft
