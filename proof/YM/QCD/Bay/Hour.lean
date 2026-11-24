import YM.QCD.Bay.Deck
/-! # Crop rotation -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Bay
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.Local
open Jets Sun Revolve Garden Strut LeafM Set Metric
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {F:ℕ}{f c: Side} {s:Strut f}{u:Site f→ℂ} {P:Spike}{δ A B:ℝ}

namespace Strut
def swing (s : Strut f) (X : Pulse f): Pulse f:=
   (fun i=> Leaf.Paths.strand X ((posDir i.2).rotate s.1) (act s i.1),fun i=> Leaf.Paths.strand X (((posDir i.2).rotate s.1).rev) (act s (i.1+step i.2)))
lemma still (s:Strut f)(U:Grid f):s.swing (settled U)=settled (s.sky U):=by
   unfold swing; apply Prod.ext
   · funext i; exact Leaf.Paths.string ..
   funext i
   change Leaf.Paths.strand (settled U) _ _=star (colour (sky s U i)); rw [Leaf.Paths.string, show act s (i.1+step i.2) = affine s.1 s.2 i.1 + ((posDir i.2).rotate s.1).vec from affine_add _ _ _ (posDir _), Step.read_rev]; rfl
lemma bendD (s: Strut f):Differentiable ℂ s.swing:=by
  unfold swing; apply Differentiable.prodMk <;> exact differentiable_pi.mpr fun i=> Leaf.Paths.reachC _ _
lemma stasis (s:Strut f)(X :Pulse f)(h:X∈Kingdom f δ) : swing s X∈ Kingdom f δ:=by
   obtain ⟨U,hU⟩:= mem_iUnion.mp h; apply Set.mem_iUnion.mpr; refine ⟨s.sky U,?_⟩
   rw [← still, mem_ball,dist_eq_norm]; rw [mem_ball,dist_eq_norm] at hU; apply lt_of_le_of_lt _ hU; rw [Prod.norm_def]; apply max_le
   · exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i=> Leaf.Paths.strand_p ..
   exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i=> Leaf.Paths.strand_p ..
lemma gold (h:Warrant s u P) (x) (g:su.El): Commute (lightP s P u x) (touch (colour g)):=by unfold Commute SemiconjBy lightP; rw [Matrix.mul_smul,Matrix.smul_mul, (interlace _ _).eq] -- orientation
lemma ring_gold (h:Warrant s u P)(x)(g:su.El): Commute (star (lightP s P u x)) (touch (colour g)):=by
    have hp:=gold h x g⁻¹; unfold Commute SemiconjBy at *; have hu:=congr_arg star hp; simp only [star_mul, touch_star, colour_inv,star_star] at hu; exact hu.symm

def tips (s:Strut f) (t:Site f→ℂ) (W:Spike) (x y:Site f) (X:Pulse f→Bundle): Pulse f→Bundle:=fun M=> star (lightP s W t x)* X (swing s M)*lightP s W t y

lemma pockets {x y:Site f}{U:Support f}{M:Pulse f→Bundle} (h:Crop x y δ U M A) (hp:Warrant s u P): Crop (act s x) (act s y) δ (U.image (act s)) (tips s u P x y M) A:=by
 obtain ⟨ha,hb,hc,hd,hf,hg⟩:=h
 have ht j : ‖lightP s P u j‖≤1:=rotation_price (license hp j)
 refine ⟨ha, fun z=> ?_,fun z hv=> ?_,fun z hv=> ?_,fun U₀ V H=>?_,fun U z=>?_⟩
 · exact ⟨mem_image_of_mem _ (hb z).1,mem_image_of_mem _ (hb z).2⟩
 · exact (((hc _ (stasis s z hv)).comp z (bendD s z)).const_mul _).mul_const _
 · unfold tips; apply (norm_mul_le ..).trans; refine (mul_le_of_le_one_right (norm_nonneg _) (ht _)).trans ?_; apply (norm_mul_le ..).trans; have he: ‖star (lightP s P u x)‖≤1:=rotation_price (Unitary.star_mem (license hp x)); exact (mul_le_of_le_one_left (norm_nonneg _) he).trans (hd _ (stasis s z hv))
 · simp only [comp_apply,tips,still]; rw [show M (settled (s.sky U₀))=M (settled (s.sky V)) from hf _ _ (agrees_pull s.1 s.2 H)]
 simp only [tips, still]; unfold sky; rw [pull_gauge,hg]; let d := turnSites s.1 s.2; rw [show colour (z (act s x))=colour ((z ∘ d) x) from rfl, show colour (z (act s y))=colour ((z ∘ d) y) from rfl]; rw [← mul_assoc,← mul_assoc, (ring_gold hp x _).eq]; simp only [mul_assoc]; have hh:= gold hp y ((z ∘ d) y)⁻¹; rw [colour_inv,← touch_star] at hh; rw [hh.symm.eq]
end Strut
end YM.QCD.Bay
