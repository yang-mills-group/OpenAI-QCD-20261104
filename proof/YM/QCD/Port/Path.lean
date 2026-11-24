import YM.QCD.Port.Pier
/-! # Root reads carry prizes. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Port
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.Local
open Jets Sun Revolve Garden Bay Strut LeafM Paths
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c f:Side}(r: Ratio c f) {v η A t:ℝ} {B b:ℕ} {D:St c}{X:Land c (Site c) (Site c)}{Y:Pays c (Site c) (Site c)}
variable {p q:Site c} {W:Support c}{G:Pulse c→Bundle}
lemma costP (h:Crop p q η W G A)(hu:v≤1)(ht:(3:ℝ)^r.count.val*v ≤ η) : Crop (r.embed p) (r.embed q) v (rig r W) (G ∘ warp r) A:=by
  obtain ⟨hp,hq,hc,hd,hv,hG⟩:=h; refine ⟨hp,fun h=> ?_,fun i hi=>(hc _ (turnout r hi hu ht)).comp i (warping r i),fun i hi=> hd _ (turnout r hi hu ht),fun U V H=>?_,fun U k=>?_⟩
  · exact ⟨halo_subset _ _ (mem_image_of_mem _ (hq h).1),halo_subset _ _ (mem_image_of_mem _ (hq h).2)⟩
  · simp only [comp_apply,posedW]; exact hv _ _ (firm r H)
  simp only [comp_apply,posedW,framed_c,hG]
lemma mosaics {G H J :Type*} [Fintype H][Fintype J][DecidableEq J][AddCommMonoid G] (q:H→J)(X:H→J→G) : ∑ j,∑ i∈(univ.filter (q · = j)), X i j=∑ i,X i (q i):=by
   simp_rw [sum_filter]; rw [sum_comm]; exact sum_congr rfl fun i _ => by simp
lemma rootedP (h:Own c η t b D A)(hu:v≤1)(ht:(3:ℝ)^r.count.val*v ≤ η)(he:r.count.val*(b+1) ≤ B)(hp:0≤t): Heritage r.embed r.embed v t B (D ∘ lowC r) A:=by
  obtain ⟨X,Y,h⟩:=h
  let W F:=univ.filter (rig r · = F)
  let Z (i j:Site c)(S):=∑ F∈W S, X i j F ∘ warp r
  let V (i j:Site c)(S):=∑ F∈W S,Y i j F
  have H i j: duel V i j t B ≤ duel Y i j t b:=by
    unfold duel; simp_rw [V,mul_sum]
    rw [show ∑ S,∑ F∈W S,rent t B _*Y i j F=∑ F,rent t B (rig r F)*Y i j F from mosaics (rig r) (fun i' j'=>rent t B j'*Y i j i')]
    exact sum_le_sum fun i' _=>mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (coversB r _ he)) hp)) (h.crop i j i').1
  refine ⟨Z,V,⟨?_,?_,fun i=> (sum_le_sum (fun j _=> H i j)).trans (h.spends i),fun j=> (sum_le_sum (fun i _=>H i j)).trans (h.dues j)⟩⟩
  · intro i j S; exact Crop.cluster _ fun F hF=> (mem_filter.mp hF).2 ▸ costP r (h.crop i j F) hu ht
  intro i j U; simp only [Z,Finset.sum_apply,comp_apply,posedW]; rw [show ∑ y, ∑ i'∈W y,X i j i' _=∑ i', X i j i' (settled (lowC r U)) from mosaics (rig r) (fun i' _=>X i j i' (settled (lowC r U))),h.sells]
variable {L:Side}{j k:ℕ} (P:Plan j)
lemma quest (ht:0≤t)(L: Side): ∃ N:ℕ,∃ δ C:ℝ,0 < δ∧0 < C∧∀ (s f: Side)(S:Ratio s f), S.count=L→∀ B:ℕ,N≤B →∀ K:Train j, Heritage S.embed S.embed δ t B (wood P 0 K ∘ lowC S) C:=by
   obtain ⟨x,C,n,δ,H⟩:= quantified P t ht
   let b:=2*n; let θ:=min 1 (δ/3^L.val)
   have he:=H.hd; let Q:= 4*padage P t x C n
   refine ⟨L.val*(b+1),θ,1+|Q|,lt_min (by norm_num) (by positivity),by positivity,fun s f S hv B hz K=>?_⟩
   obtain ⟨W,h⟩:= stroller (0: Site s) P K H (p:=0) le_rfl
   exact (rootedP S h.all.1 (min_le_left ..) (by rw [hv,mul_comm]; exact (le_div_iff₀ (by positivity)).mp (min_le_right ..)) (by rw [hv]; exact hz) ht).mono ((le_abs_self Q).trans (le_add_of_nonneg_left zero_le_one))
lemma faithful (w : Train j): Tow r (dot r) (dot r) (wood P 0 w ∘ lowC r):=by
   refine ⟨fun u d T U ht => ?_⟩; have he:= mist r u ht; simp only [comp_apply,pulled]; exact spin_wood he.1 he.2 w P (lowC r U) -- args
end YM.QCD.Port
