import YM.QCD.Jets.Deluxe
/-! # choosing the overlap roof. Include inspections. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Jets.Touch
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.AbsoluteSums Footprint Trees
open Sun ConnectedActivityE6 Pressure Animals Garden
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {F j k:ℕ}{L:Side} {x u v a b c ν C D T θ w κ q Y ε e z: ℝ} {i m:ℕ}

section
variable {f c: Side}{r:ℕ}{E J D: Type} {S:Ratio c f} (G:Send S F D)(P:Rise f F E J)
-- Choose W halo B coarse AFTER projections, so that any sum of supports read true. `f≥`. Price unaffected as long conversion reserve

def roof (m B:ℕ)(i:Fj D E J): Support c:=enlargement S m B (inspected (brim G P i))

lemma depart (B:ℕ)(h:G.trim ≤ B)(he: 0<B)(i:Fj D E J): (brim G P i).image S.parent ⊆ enlargement S 3 B (native G P i):=by
  intro j hj; obtain ⟨m,hm,rfl⟩:= mem_image.mp hj; obtain ⟨a,ha,hx⟩:= halo_spec.mp hm
  refine halo_spec.mpr ⟨S.parent a, mem_image_of_mem _ ha,?_⟩; have h := YM.Work.E04.parent_separation S a m; omega
lemma roofs (m B:ℕ) (h:G.trim ≤ B)(ht:0<B): Count G P (roof G P m B) ∧ ∀ i,roof G P m B i ⊆ enlargement S (m+8) B (native G P i):=by
  constructor
  · exact ⟨fun i=>Subset.trans (image_subset_image (subset_union_left (s₂:=_) : brim G P i⊆inspected (brim G P i))) (halo_subset ..)⟩
  intro i a he; obtain ⟨j,hj,hx⟩:= halo_spec.mp (inspected_price S m B _ ht he)
  obtain ⟨b,hb,hh⟩:= halo_spec.mp (depart G P B h ht i hj)
  refine halo_spec.mpr ⟨b,hb,(separation_triangle b j a).trans ?_⟩; rw [Nat.add_mul] at hx ⊢; omega
end
end YM.QCD.Jets.Touch
