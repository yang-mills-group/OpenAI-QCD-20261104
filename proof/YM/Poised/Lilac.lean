import YM.QCD.Purse.Home
/-! # Fit short-pick upper; furnish all Pack constructors. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Jets.Touch
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.AbsoluteSums Footprint Trees
open Sun ConnectedActivityE6 Pressure Animals Garden
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {F j k:ℕ}{L:Side} {x u v a b c ν C D T θ w κ q Y ε e z: ℝ} {i m:ℕ}{f g: ℝ→ℝ}

lemma diamondsP (P:Plan j)(F K₂:ℕ)(hj:4≤j)(hk :4 ≤k)(K:ℝ)(hK:0<K):∃ i:ℕ,∀ L:Side,i≤L.val→∀ (w r q a:ℝ),0<w→0<r →∀ b:ℕ,∀ᶠ x in atTop,
    let t:= haloK L x; let δ:=coneK L w x
    ∀ (C f: Side),2*(radiusB x+1)< f.val→∀ (G:Flight j k)(H:f.val=C.val*G.L.val),G.L=L→ ∀ (v X A b' Q m:ℝ)(Z:Offer 1 X A)(U:Offer 2 b' Q), |m|≤t→
       ∀ p:Sun G C f H δ v q r a b (pesto P G H (trunkM Z U t m f)), ∃ η, Fork.Sea G H (radiusB x) δ η q (fiery su x L) p.Z p.V K₂ ∧ K*fingers F*η ≤ Kit.slope L:=by
  obtain ⟨C,hc,h⟩:=Fork.sizesP (j:=j) P hj hk K₂
  obtain ⟨i,hi⟩:= exists_nat_gt (2*K*fingers F*C)
  obtain ⟨A,hA,ha⟩:= Fork.travelQ
  refine ⟨i, fun L hl w r q a hW hr b=> ?_⟩
  filter_upwards [filming L hW A, (sol L P C q A a r w hW hr b K₂|>.mul_left (K*fingers F)).below (by norm_num) (Kit.slope L/2) (by unfold Kit.slope; positivity), Delay.shift_pos su L] with x hx hp hX
  intro t δ c f hB G H hL v R D b' Q m Z U hm p
  let s:=radiusB x; let B:=tabP P G.L C q A a r v |m| (fiery su x L) δ K₂ s b
  have hw : 0<δ:=p.positive
  have he : 0 < fiery su x L:=mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr hX)) (Real.exp_pos _)
  refine ⟨B, horns s K₂ b hr he.le hw p.stable p.Z0 p.V0 (h G f c H) hA hx (fun u i he'=> ha _ _ _ u i hB he.le he'),?_⟩ -- x binder likely unknown; fiery G.L? horns estate uses travel with t. 
  have hV : B ≤ tabP P L C q A a r 0 t (fiery su x L) δ K₂ s b:=by
      unfold B; rw [hL]; unfold tabP
      have hb:=p.stable.calf; have hv:=healthy P L; have hx:= mass_pos L -- fill
      gcongr
  apply le_trans (mul_le_mul_of_nonneg_left hV (by unfold fingers; positivity)); have hp₁:0 < (L.val:ℝ):=by positivity
  have hv: 0 < Kit.slope L:=by unfold Kit.slope; positivity
  have ht: K*fingers F * (C*Kit.slope L/(L.val:ℝ)) ≤ Kit.slope L/2:= by
    rw [←mul_div_assoc,div_le_iff₀ hp₁]; nlinarith only [mul_le_mul_of_nonneg_right (hi.le.trans (show (i:ℝ)≤L.val by exact_mod_cast hl)) hv.le]
  have hh : K*fingers F * (tabP P L C q A a r 0 t (fiery su x L) δ K₂ s b-C*Kit.slope L/(L.val:ℝ)) ≤ Kit.slope L/2:= (le_abs_self _).trans hp; rw [mul_sub] at hh; linarith
end YM.QCD.Jets.Touch
