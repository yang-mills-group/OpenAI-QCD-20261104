import YM.Rill.Audio
/-! Two-scale layout. The stencil on periodic copies is paid at the larger pitch; arbitrarily many extra insertions at finer pitch. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tarn.Quilt
open YM.Analysis YM.Fir Fir Fir.Gains Fir.TagF Filter Set Metric
open Lattice Cells Lyre QCD QCD.Lat QCD.Tide QCD.Grass QCD.Plum QCD.RP QCD.Revolve UV Needle Patria Patria.Depth Patria.Hub Poised Plans Plans.Stamp Intag Intag.Vale Romance
open scoped Topology ContDiff BigOperators Classical ComplexOrder
open Function Sash TorusPCAC.Geometry Finset Goblet YM.Next.Rank.Station
variable {n c l:Side} (τ: Ratio c n) (v:Ratio c l) (w:Ratio l n) (ht:Even c.val)(h:Even l.val)(hx:Odd v.count.val)(hv:Odd w.count.val)
include h ht hx hv
-- full chamber batching. Subtile fit.See anchored nearest.
lemma tucked (x:Site n)(p:Site l) : ∃ z:Site c,(mural w h x).chamber p ⊆ (mural τ ht x).chamber z:=by
    have hB:= midway v hx p; let f:= v.parent p; refine ⟨f,fun i hi=>?_⟩
    have hτ:= Intag.odd_v v w τ ht hx hv; have hF:separation i (x+w.embed p) ≤ w.count.val/2:=by
       rwa[← zero_margin (mural w h x) p rfl,key_margin w _ _ _ _ hv, Nat.add_zero] at hi
    have he:= separation_triangle i (x+w.embed p) (x+τ.embed f); have hy: separation (x+w.embed p) (x+τ.embed f)=w.count.val*separation p (v.embed f):=by
        rw [embed_comp v w τ]; change pdist (_-_)= _; rw[add_sub_add_left_eq_sub]; exact both .. -- helper namespace
    have hk: separation p (v.embed f)≤ v.count.val/2:= by unfold f; omega
    have hP:=mul_le_mul_right' hk w.count.val
    rw [← zero_margin (mural τ ht x) f rfl,key_margin τ _ _ _ _ hτ,Nat.add_zero, Intag.vaneP v w τ hx hv]; exact he.trans (by rw [hy]; exact (add_le_add hF (Nat.mul_le_mul_left _ hk)).trans_eq (Nat.add_comm ..))
-- first small translation then lift charge. Constraint large-cell margin M=l.count·(s count(level j+1→ℓ)*3 + ?? costs). choose balm coarse margin w.r.t k done before refinement, waste inter.
variable {I J:Type}[Fintype I][Fintype J] (x:I→ Site n)(y:J→ Site n) (C D:ℕ)
lemma joints (hc: Fintype.card I*(2*(C+1))< v.count.val)(hD: Fintype.card J*(2*D)<w.count.val)(hz:0 < D):∃ z:Site n, (∀ i,∃ p:Site c,x i∈(mural τ ht z).margin p (w.count.val*C))∧∀ j,∃ p:Site l,y j∈(mural w h z).margin p D:=by
    obtain ⟨a,ha⟩:=Vent.balm w h y D hz hD; let U(i):= w.parent (x i-a); obtain ⟨b,hb⟩:=Vent.balm v ht U (C+1) (Nat.succ_pos _) hc
    let z:= a+w.embed b; have he:=odd_v v w τ ht hx hv; refine ⟨z,fun i=>?_,fun j=>?_ ⟩
    · obtain ⟨p,hp⟩:= hb i; refine ⟨p,(key_margin τ z (x i) p ht he _).2 ?_ ⟩; have h:= (key_margin _ _ _ _ _ he _).1 ((stepSpan v w τ b (U i) p ht hx hv _).1 hp)
      have hp:=separation_triangle (x i-a) (w.embed (U i)) (w.embed b+τ.embed p); have hq:2*separation (x i-a) (w.embed (U i))<w.count.val:=midway w hv _; rw [show separation (x i) (z+τ.embed p)=separation (x i-a) (w.embed b+τ.embed p) from (by unfold separation z; congr 1; abel)]; rw [Nat.mul_succ] at h; omega
    obtain ⟨p,hp⟩:= ha j; refine ⟨p-b,(Goblet.margV w h a b (p-b) hv _ D).mp ?_⟩; rwa [add_sub_cancel] -- lemma
end YM.Massive.Tarn.Quilt
#print axioms YM.Massive.Tarn.Quilt.tucked
#print axioms YM.Massive.Tarn.Quilt.joints
