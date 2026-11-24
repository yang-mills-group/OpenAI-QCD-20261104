import YM.TIPS.Reg
import YM.Infer.Bravo
import YM.Elms.Orient
import YM.Eden.Unit
import YM.TIPS.Prep
import YM.Eden.Pre
/-! # launch calibrated single-site arrays form. Imports.Engine.P EP stronger pre. Finance θ^q cover.Part.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Evo
open Function Lattice Wilson RG Metric Precision Bloch Laurent Tensor Work.F03 Exterior
open Finset Filter Matrix AnalyticBridge.LocalGaussianLaws.Current
open YM.Next.Free YM.Bloom YM.Arise YM.Arise.Range Bloom.TreeP
open scoped Topology BigOperators InnerProductSpace Matrix Matrix.Norms.L2Operator TensorProduct Classical
variable {G:Gauge}{d k i m j l w r g q N:ℕ}{c f n:Side} {H:Bed}{t:Clip}{a b:ℝ}{I J :Type}[Fintype I][Fintype J]
open Massive UV QCD QCD.Eden QCD.Grass QCD.Cove Lat Poised.Display
open Elm Elm.SparK Elm.SparK.Arbor Elm.SparK.Arbor.Gallery Elm.SparK.Arbor.PrismD Poised Papyrus Lining
open Poised.Plans RP YM.Source YM.Source.Drops QCD.Anomaly QCD.Creek YM.Eden Girdle Sieve Counting Counting.Terrain Pipes Facets Orientation MassiveQCD.Plate Carte.Hem Permit
variable (p:UV.Label d)(Q:SourceRead.TaperHol)(K:Hol su)(V: Lining.Temper.Collage.Exhibit K)(hk:Drops.Peg K (d/2))(hp:p.val∈Rtg d i g q)
local notation "P"=>Arise.Range.introduce d p.val
local notation "Zp"=>Gallery.polarity q
variable {P₀:BudgetPoint}{v θ:ℝ}

variable (ε:ℝ) (he:0<ε)
include V K Q hp hk he
omit V K Q hp hk he
open scoped Stamp
open QCD.Acre QCD.Acre.Stratum.MarchQ QCD.Acre.Stratum.MarchQ.Tribute QCD.Acre.Stratum.MarchQ.Tribute.Nacre Arbor
-- nonnull of matched.Any density.V spectrum. P spans
lemma innerPrototype (p:Label d) (he:0<ε)(h:p≠0):∃ r z:ℝ,0<r∧0<z∧∀ (q:Label d)(O:BudgetPoint)(v:ℝ), ‖prism O.threshold v d (passport d q)-(passport d p : Mini d)‖ < r → ‖dimming O.threshold v d q-p‖ < ε ∧ z< wealth q.val O.threshold v:=by
     obtain ⟨C,hC,hQ⟩:= prestige d; have hN:0<C:=zero_lt_one.trans_le hC; obtain ⟨W,hW,hn⟩:=LinearMap.exists_antilipschitzWith (passport d) (LinearMap.ker_eq_bot.mpr (Gallery.bank d)) -- namespace
     have hf: 0<‖p‖:= norm_pos_iff.mpr h; let L:=max W.val (1:ℝ); have hL:1≤ L:=le_max_right ..; have hx:0<L:=zero_lt_one.trans_le hL
     let u:=min ε (‖p‖/2); have ht:0<u:= lt_min he (half_pos hf); refine ⟨u/L, (‖p‖/2)/C, div_pos ht hx, div_pos (half_pos hf) hN,fun q O v h=>?_⟩
     let w:=dimming O.threshold v d q; rw[Gallery.transferQ] at h; have hm: ‖w-p‖<u:=by
           have hy: ‖w-p‖ ≤ (W:ℝ)*‖passport d (w-p)‖:=hn.le_mul_norm (map_zero _) _
           have hp: ‖passport d (w-p)‖<u/L:=by rw [map_sub]; exact h
           exact hy.trans_lt (((mul_le_mul_of_nonneg_right (le_max_left (W:ℝ) (1:ℝ)) (norm_nonneg _)).trans_lt (mul_lt_mul_of_pos_left hp hx)).trans_eq (by field_simp; rfl))
     have hh:‖p‖ /2 < ‖w‖:=by have ht:=norm_sub_norm_le p w; rw [norm_sub_rev] at ht; linarith [hm.trans_le (min_le_right ..)]
     refine ⟨hm.trans_le (min_le_left ..),(div_lt_iff₀ hN).mpr ((hh.trans_le (hQ ..)).trans_eq (mul_comm ..))⟩
-- accuracy in b-economic.P_final using h_b. takes ε pre choose uniform for all reflections.Expositor.
lemma gripW (ε p:ℝ)(hp:0 < ε) (C:ℝ) (h:1 ≤ C) :∃ w:ℝ,1 ≤ w∧∀ a:ℝ,w ≤a→ p*(1/(2*a)*C)< ε:=by
    let b:=max 1 p; have hb:1 ≤ b:=le_max_left ..; let A:=max (b*C/ε) 1; have hy:1 ≤ A:=le_max_right ..; refine ⟨A,hy,fun a ha=>?_⟩; have hx:0 < a := zero_lt_one.trans_le (hy.trans ha); refine (mul_le_mul_of_nonneg_right (le_max_right 1 p) (by positivity)).trans_lt ?_; rw [show b*(1/(2*a)*C)=b*C/(2*a) from by ring]; apply (div_lt_iff₀ (by positivity)).mpr; have hh:= (div_le_iff₀ hp).mp ((le_max_left _ _).trans ha); nlinarith only [hh,hx,hp]
end YM.Massive.Evo
#print axioms YM.Massive.Evo.innerPrototype
#print axioms YM.Massive.Evo.gripW
