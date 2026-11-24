import YM.QCD.Globe.Gull
import YM.QCD.Nola.Wheat
import YM.QCD.Nola.Arch
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Globe
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Pine YM.Next.Free Leaf LeafM Tee Garden Entr Kites
variable {f c:Side}{j k m N:ℕ}{S:Flight j k} {h:f.val=c.val*S.L.val}{p:BudgetPoint}
open Fork
-- special lifts through signed
variable (t:Signed)(v:Site c)
def foam (s:Signed)(x:Site c):Cover:= s⁻¹.act (lift (s.act x))
lemma foams : wrap c (foam t v)=v:=by unfold foam; rw [← wrap_signed,wrap_lift, Signed.inv_act]
lemma foamy : foam 1 v=lift v:=by unfold foam; rw [inv_one]; simp
lemma assays (s t:Signed): foam t (s.act v)=s.act (foam (t*s) v):=by
    unfold foam; rw [← Signed.act_mul,mul_inv_rev,Signed.act_mul,Signed.act_mul,Signed.act_inv]
lemma foam_cost (i:Axis): ((foam t v) i).natAbs ≤ pdist v:=by
    obtain ⟨j,rfl⟩:= t⁻¹.perm.surjective i; unfold foam; rw [Signed.act_at]; have he := (component_le (t.act v) j).trans_eq (pdist_invariant t v); split <;> omega
lemma foam_near (hn:10*pdist v<c.val): foam t v=lift v:= by
     have ht :∀ i,-(c.val:ℤ) < 2*foam t v i ∧ 2*foam t v i ≤ c.val:=by intro i; have h:=foam_cost t v i; omega
     exact (lift_eq_iff.mpr ⟨(foams t v).symm,ht⟩).symm
lemma oaub (u: Cover)(x:Site c): occ x u*occ x u=1∧star (occ x u)=occ x u:=⟨(realSeam ..).2,(realSeam ..).1⟩
lemma folios (x: Cover)(p:Site c) : occ (p+wrap c x) (-x)=occ p x:=by
    have he :=Flume.sign_rate p x (-x); rw [add_neg_cancel,show occ p 0=1 from ?_] at he
    · apply mul_left_cancel₀ (show occ p x≠0 from norm_pos_iff.mp (Eq.symm (Flume.pathLength p x) ▸ zero_lt_one)); rw [← he, (oaub x p).1]
    unfold occ; rw [route_same]; rfl
-- compare affinity
lemma helmet (x:Site c)(u:Strut c)(y:Cover)(K:Spike)(g:Site c→ℂ)(hp: Warrant u g K):
   occ (act u x) (u.1.act y)*g x=g (x+ wrap c y)*occ x y:=by
    let w:=route 0 y 1
    have he:stop (0:Cover) w=y:=route_end ..
    have h : shimmer 0 x w * g (x+wrap c y)= g x* shimmer 0 (act u x) (w.map (·.rotate u.1)):=by rw [show x+wrap c y=stop x w from (by rw [wrap_stop,he])]; exact flare_path hp.1 ..
    have hh:= moved_stop u.1 (0:Cover) w; rw [he,Signed.act_zero] at hh; rw [Quarry.occ_rays,Quarry.occ_rays,← hh,he] at h; rw [mul_comm _ (g x),← h,mul_comm]
end YM.QCD.Globe
