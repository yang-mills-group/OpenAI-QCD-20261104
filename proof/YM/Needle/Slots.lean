import YM.Needle.Form
/-!
  Pairing against the detector in checked reads at an arbitrary smaller maturity.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Needle
open Set Function Filter Lattice Cells Lyre Lyre.Goblet Romance QCD QCD.Lat QCD.Tide QCD.Grass Plum QCD.RP Patria Patria.Depth Patria.Hub Intag Intag.Vale
open Finset UV Poised Poised.Plans Poised.Plans.Stamp Poised.Stative
open scoped Topology ContDiff BigOperators Classical ComplexOrder
variable {C:Sequence} (P:Calibration C) {d:ℕ}(Z:Laurel d) (J:Landing P.sym Z)
local notation "S"=> C.S
set_option quotPrecheck false
local notation "nᴮ" i:arg => C.S.side (C.R i) (C.N i)
local notation "a" i:arg=> C.S.spacing (C.N i)
variable {β ν:ℝ}(hC:C.Path β ν)
open CardsT
-- Earned checked insertion family. any label.
abbrev Basket (C:Sequence) (w: (i:ℕ)→stalk C i)(u:Averaging):Prop:=∀ᶠ j in atTop,∃ ℓ:ℕ,∃ hj:j ≤ ℓ,∃ Vv:ℝ,0 ≤ Vv∧∀ᶠ i:ℕ in atTop,∀ (hp:ℓ≤ C.N i)(he:Even ((C.R i).val)),let R:= C.R i; ∀ x:Site (C.S.side R ℓ),∀ y:Site (C.S.side R j),∀ b:Cover,wrap _ b∈ (mural (viewW C.S R hj) (evenW C.S R he j) x).margin y (Tarot.Vista.marginM C.S 16 j ℓ) → Gold (C.A i).regulator (Column.sky C.S R j (C.N i) (hj.trans hp) (evenW C.S R he j) x) y (CardsT.checkedT u (ratioTo C.S (C.N i) ℓ) (w i) b) Vv
variable {P Z J} (E:Invest P d)
namespace GaugeP
variable (K: GaugeP P Z J)(i j ℓ:ℕ)(hj:j≤ℓ)
local notation "B₀"=> viewW C.S
variable (hv:Sway C.S)(G:Capital P d 1)
include G hv
lemma coverT:∀ᶠ j in atTop,∃ Vv:ℝ,0≤Vv ∧ 6 ≤ (C.S.step j).L.val∧ ∀ᶠ i:ℕ in atTop,∀ v:Stokes d, GreenP C i j (K.heads i v) Vv:=by
    filter_upwards [G.gains (v:=K.price),hv.high.eventually_ge_atTop 6] with j hj h; refine ⟨K.price*Hub.rayM C.S d 1 G.v j,mul_nonneg K.realH (G.power _),h,?_⟩; filter_upwards [hj,K.tall] with i hi hh v; exact hi _ (hh v).1
omit G hv
-- center slots aligned
open Intag
include hj
lemma lawn (he:Even ((C.R i).val))(hi:ℓ ≤ C.N i)(hB:j+1 ≤ C.N i)(hp:6 ≤ (C.S.step j).L.val): 0∈ (Column.sky C.S (C.R i) j (C.N i) (hj.trans hi) (evenW C.S (C.R i) he j) (0:Site (C.S.side (C.R i) ℓ))).margin (0:Site (C.S.side (C.R i) j)) (3*(viewW C.S (C.R i) hB).count.val):=by
     unfold Column.sky Column.pillar; rw[dif_pos hi, Intag.key_margin _ _ _ _ _ (viewOdd ..)]
     simp [Ratio.embed]; change 3*ratioTo C.S (C.N i) (j+1) ≤ ratioTo C.S (C.N i) j/2; rw [step_factor hB]; have h:= Nat.mul_le_mul_right (ratioTo C.S (C.N i) (j+1)) hp; omega
omit hj
variable (u:Averaging)(w:(i:ℕ)→stalk C i)(hB: Basket C w u)
include G hv hC hB
local notation "g"=>K.goalJ
local notation "Rᴮ" i:arg => (C.A i).regulator
set_option maxHeartbeats 900000 in
lemma testPack :∃ Vv:ℝ,0 ≤ Vv ∧ ∀ᶠ i:ℕ in atTop,∃ O:Merit K i,‖O.testR (w i)‖≤ Vv:=by
     obtain ⟨N,h⟩:=eventually_atTop.mp ((K.coverT hv G).and hB); obtain ⟨j,hj,hX⟩:= shyness hC _ (show 0<K.extent/202 from by have h:=K.breadth; positivity) N
     have hφ:202*C.S.spacing j≤ K.extent:=by have hc:= (lt_div_iff₀ (by norm_num: (0:ℝ) < 202)).1 hX; linarith only [hc]
     obtain ⟨⟨Q,hQ,hL,hG⟩,ℓ,hj,V,hv',hP⟩:= h j hj
     refine ⟨Q*V,mul_nonneg hQ hv',?_⟩; filter_upwards [hC.uv.tendsto_atTop.eventually_ge_atTop ℓ,hC.uv.tendsto_atTop.eventually_ge_atTop (j+1),K.nonzeroV hC j ℓ hj hφ,hG,hP] with i hi hk hν hz hM -- order nonzero.
     obtain ⟨O,hO⟩:= notch K i j ℓ hj hφ hi u (w i)
     let Rι:=C.R i; let Pᵢ:=C.S.side Rι j; let Kᵢ:=C.S.side Rι ℓ; let b:=goalL K j ℓ; let b':= wrap Pᵢ (K.goalJ j)
     let hE:= hC.even i; let T:= Column.sky C.S Rι j (C.N i) (hj.trans hi) (evenW C.S Rι hE j) (0:Site Kᵢ)
     refine ⟨O,(pi_norm_le_iff_of_nonneg (mul_nonneg hQ hv')).2 (fun t=>?_)⟩; rw [hO]
     let Z:= (heads K i t); let p:Fin 2→T.Cell:=![0,b']; let W:= V; let v:Fin 2→ℝ:=![Q,W]
     let Y:= CardsT.checkedT u (ratioTo C.S (C.N i) ℓ) (w i) b; let X: Fin 2→Insertion (C.S.side Rι (C.N i)) 6:=![Z 0, Y]
     have hX₀: wrap (C.S.side Rι (C.N i)) 0∈ T.margin 0 (3*(viewW C.S Rι hk).count.val):=by rw [map_zero]; exact lawn i j ℓ hj hE hi hk hL
     have hp': Injective p:=by intro x y he; fin_cases x <;> fin_cases y <;> first | rfl | exact False.elim (hν he.symm) | exact False.elim (hν he)
     have hh : ∀ j:Fin 2, Gold (Rᴮ i) T (p j) (X j) (v j):=by
        intro j'; fin_cases j'; · exact hz t hk T rfl rfl _ _ hX₀
        exact hM hi hE 0 b' b (joinsC (viewW C.S Rι hj) (evenW C.S Rι hE j) (K.goalJ j) (viewOdd ..))
     change ‖(Rᴮ i).average (Z 0 * Y)‖ ≤ Q*V; simpa only [X,Z,p,v,W,Fin.prod_univ_succ,List.ofFn_zero,List.ofFn_succ,List.prod_nil,List.prod_cons,mul_one,Finset.univ_eq_empty,Finset.prod_empty, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ] using Gold.value p hp' X v hh rfl rfl ((hC.normalized i).beta_pos (Nat.le_refl _) |>.le) (sideW hC i _) (engaged hC i)
end GaugeP
end YM.Massive.Needle
#print axioms YM.Massive.Needle.GaugeP.testPack
