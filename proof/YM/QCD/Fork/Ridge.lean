import YM.QCD.Leaf.Treasury
import YM.QCD.Garden.Quiver
import YM.Work.E08
/-! # extracting thick sewn packs with respect to any fine endpoint. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Fork
open Lat Kit Lattice Wilson RG Run Leaf Tee Function Finset Metric Filter
open Orbit Flume Sparks Quarry Pine QCD.Cost Eyrie Revolve Rudder
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical
variable {I V: Type*}[Fintype I] [Fintype V] {L f:Side}{D E:Type} [Fintype D] [Fintype E]
variable {x y : Site f}{a:Slot}{ξ t p C D':ℝ}{u:I→Site f}{v: V→Site f}{U: Support f}{B b m:ℕ}{H:Grid f→ArrayL I V}{X:Land f I V}{Y:Pays f I V}
-- use fiber pack dim fine and coarse exposed
lemma wide (h:x∈U)(ht: ¬ U⊆ Lattice.halo b {x}): b < coverNumber m U*(4*m+2)+2*m:=by
  obtain ⟨y,hy,hz⟩:= Finset.not_subset.mp ht
  have hp : b < separation x y := lt_of_not_ge fun H=> hz (halo_spec.mpr ⟨x,mem_singleton_self _,H⟩); exact hp.trans_le (Corona.extent _ _ h hy)

def trunkFt (x:Site f)(b:ℕ):Support f:= Lattice.halo b {x}
def shortZip (x: Site f)(b:ℕ): Finset (Support f):=univ.filter fun U=> U ⊆ trunkFt x b

def spoon (X:Land f I V) (q:Site f)(b:ℕ) (i:I)(j:V): Pulse f→Bundle:=∑ U∈shortZip q b,X i j U
def charge (Z:Pays f I V)(q:Site f)(b:ℕ)(i:I)(j:V):ℝ:=∑ U∈shortZip q b, Z i j U
lemma wider_c {F:Pulse f→Bundle}{W:Support f}(h:Crop x y ξ U F C)(hv:U⊆W): Crop x y ξ W F C:=by
  obtain ⟨a,b,c,d,g,e⟩:=h; exact ⟨a,fun u=>⟨hv (b u).1,hv (b u).2⟩,c,d,fun i j ht=> g i j (agrees_mono ht hv),e⟩
lemma trimming (h:Pack u v ξ t B H D' X Y)(q:Site f)(b:ℕ)(i:I)(j:V): Crop (u i) (v j) ξ (trunkFt q b) (spoon X q b i j) (charge Y q b i j) := by
   refine Crop.cluster _ ?_; intro S hS; exact wider_c (h.crop i j S) (mem_filter.mp hS).2

def satZip (x:Site f) (b:ℕ): Finset (Support f):=univ \ shortZip x b
lemma purse_fee (h:Pack u v ξ t B H D' X Y)(q:Site f)(b:ℕ)(i j)(ht:0≤t): charge Y q b i j + (∑ S∈satZip q b,Y i j S) ≤ duel Y i j t B :=by
  unfold charge duel satZip; rw [add_comm, sum_sdiff (Finset.subset_univ _)]; exact sum_le_sum fun k _=> le_mul_of_one_le_left (h.crop i j k).1 (market ht _ _)
lemma produce (h:Pack u v ξ t B H D' X Y)(q:Site f)(b:ℕ)(i j)(U:Grid f): cell (H U) i j= spoon X q b i j (settled U)+ ∑ S∈satZip q b,X i j S (settled U):=by rw [← h.sells,spoon,Finset.sum_apply]; exact (by rw [add_comm,satZip,sum_sdiff (Finset.subset_univ _)])

def fossil (b B:ℕ):ℝ:= ((b:ℝ)-2*B)/(4*(B:ℝ)+2)
lemma relic (h:¬U⊆ Lattice.halo b {x}) (hp:x∈U): fossil b B < coverNumber B U:=by
   have he:b < coverNumber B U*(4*B+2)+2*B := wide hp h
   have ht: (b:ℝ) < coverNumber B U*(4*(B:ℝ)+2)+2*B:=by exact_mod_cast he
   unfold fossil; rw [div_lt_iff₀ (by positivity : 0 < 4*(B:ℝ)+2)]; linarith

lemma worthZ (h:Pack u v ξ t B H D' X Y) (i:I)(j:V) (p:Site f) (W:ℝ)(b:ℕ)(hp:p=u i ∨ p=v j)(hz:W≤ t): ∑ S∈ satZip p b,rent W B S*Y i j S≤ Real.exp (-(t-W)*fossil b B)* duel Y i j t B:=by
  let E:= satZip p b; rw [duel,mul_sum]; refine le_trans ?_ (sum_le_sum_of_subset_of_nonneg (subset_univ E) (fun a _ _=>?non)); rotate_left
  · exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (fair ..).le (h.crop i j a).1)
  apply sum_le_sum; intro L hL; by_cases ht: Y i j L=0; · rw [ht,mul_zero,mul_zero,mul_zero]
  have hg : p∈L:=hp.elim (fun he=> he ▸ ((h.crop i j L).2.1 ht).1) (fun he=> he ▸ ((h.crop i j L).2.1 ht).2)
  have hv : ¬ L ⊆ Lattice.halo b {p}:=fun hg=> (mem_sdiff.mp hL).2 (mem_filter.mpr ⟨mem_univ _,hg⟩)
  unfold rent; rw [← mul_assoc,← Real.exp_add]; apply mul_le_mul_of_nonneg_right _ (h.crop i j L).1; apply Real.exp_monotone; nlinarith [relic (B:=B) hv hg]
lemma coins (h:Pack u v ξ t B H D' X Y)(q:Site f)(b:ℕ)(i j)(ht:0≤t): charge Y q b i j ≤ duel Y i j t B:= le_trans (le_add_of_nonneg_right (sum_nonneg fun L _=> (h.crop i j L).1)) (purse_fee h q b i j ht)
lemma mismatch (h:Pack u v ξ t B H D' X Y)(i j b p)(hp:p=u i∨p=v j)(ht:0≤t)(hx:0<ξ)(U:Grid f): ‖spoon X p b i j (settled U)-cell (H U) i j‖ ≤ Real.exp (-t*fossil b B)* duel Y i j t B:=by
  rw [produce h p b i j U]; have hk:=worthZ h i j p 0 b hp ht
  simp only [sub_zero,rent,zero_mul,Real.exp_zero, one_mul] at hk; rw [← sub_sub,sub_self,zero_sub,norm_neg]
  apply (norm_sum_le ..).trans ((sum_le_sum fun L _=> (h.crop i j L).2.2.2.1 _ (citizenship f hx U)).trans hk)
end YM.QCD.Fork
