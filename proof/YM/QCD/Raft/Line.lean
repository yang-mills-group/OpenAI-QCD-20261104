import YM.QCD.Fog.Frost
import YM.Push.LOOP_COEFFICIENT.AliasJets

/-! # transport projections at the two real tori. Counting convention, W before gradient -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Raft
open Lattice Wilson Function Finset Filter Metric RG Precision Bloch Laurent
open Extra Iteration QCD.Smoke Work.F08 Work.F03 Exterior Bid Push.Loops Matrix
open scoped Topology BigOperators Matrix Matrix.Norms.Frobenius ContDiff Classical InnerProductSpace
variable {c f n:Side}{I J K:Type}[Fintype I][Fintype J]

def vw (p:Site n)(v:I→ℂ) (x:Co n I):ℂ:= cell p x.1 * v x.2
lemma vw_plane [DecidableEq I] (p:Site n)(v:I→ℂ):plane (Equiv.refl (Co n I)) p *ᵥ v=vw p v:= funext fun z=> plane_apply ..
lemma sendS {u:J→ I→ℂ} (p:Finset J) {A : Matrix K I ℂ}: A *ᵥ (∑ i∈p,u i) =∑ i∈p, A *ᵥ u i:=by
  induction p using Finset.induction_on with| empty=>simp| insert i p h hv=>rw [sum_insert h,sum_insert h,Matrix.mulVec_add,hv]
variable [DecidableEq I][DecidableEq J]
lemma vw_fetch {p:Site n}{a : Momentum} {M: Row I J}(h:M.safe) (u:J→ℂ)(ht:Matches a p): cmat (M.acts n) *ᵥ vw p u=vw p (M.read a *ᵥ u):=by simp_rw [← vw_plane]; exact (acts_routed M h ht).vector _
lemma vw_raze (g:Ratio c f)(z:Cover)(A:Cross g.count I J)(h:Row.safe A)(x:J→ℂ):
    cmat (installed g A)*ᵥ vw (wrap c z) x=∑ i:Site g.count,vw (aliasSite g z i) (profile A (quant c z) i *ᵥ x):=by
  rw [← vw_plane,mulVec_mulVec,aliasProject (g:=g) A h z]; -- distribute
  simp_rw [← vw_plane,mulVec_mulVec]; rw [sum_mulVec] -- inspect
lemma isolateS {g:Ratio c f} (z:Cover)(A:Site g.count→ I → ℂ) (v:Site g.count) :
    pick (Equiv.refl (Co f I)) (aliasSite g z v)*ᵥ (∑ i:Site g.count,vw (aliasSite g z i) (A i))=A v:=by
  rw [sendS]; simp_rw [← vw_plane,Matrix.mulVec_mulVec,pick_plane, (aliasSite_inj z).eq_iff]; rw [Finset.sum_eq_single v]; · simp
  · intro b _ he; rw [if_neg he.symm,Matrix.zero_mulVec]
  simp
lemma gotcha {g:Ratio c f} (z:Cover)(X Y: Site g.count→I→ℂ)(h:∑ i,vw (aliasSite g z i) (X i)=∑ i,vw (aliasSite g z i) (Y i)): X=Y:= funext fun i => (isolateS _ _ i).symm.trans (Eq.trans (congr_arg (fun a=> pick (Equiv.refl _) (aliasSite g z i)*ᵥ a) h) (isolateS z Y i))
-- re/im and promotion. stencil d
variable {a:Momentum}{k:ℕ}{p:Site n}
def vision (x:I→ℂ): I→ℝ:= fun i=> (x i).re
def desire (x:I→ℂ): I→ℝ:=fun i=>(x i).im
lemma see (A: Matrix J I ℝ)(v:I→ℂ): vision (cmat A *ᵥ v)=A*ᵥ vision v:=by funext i; unfold vision; simp [cmat_apply,approached, Matrix.mulVec,dotProduct, Complex.mul_re]
lemma believe (A: Matrix J I ℝ)(v:I→ℂ): desire (cmat A *ᵥ v)=A*ᵥ desire v:=by funext i; unfold desire; simp [cmat_apply,approached, Matrix.mulVec,dotProduct, Complex.mul_im]
lemma gradient_s (ht:Matches a p)(x:TypeFace k→ℂ): cmat (Exterior.d k n)*ᵥ vw p x= vw p (symbol k a*ᵥ x) :=by rw [← reading]; exact vw_fetch (cobound_safe k) x ht
lemma vapors_s (ht:Matches a p)(x:TypeFace 1→ℂ) (j:PlaqAxes):
    (symbol 1 a *ᵥ x) (plaquette j)=q a j.val.1*x (coord j.val.2)-q a j.val.2*x (coord j.val.1):=by
  let L:= cmat (Exterior.d 1 n)*ᵥ vw p x
  have he:L (0,plaquette j)=(symbol 1 a *ᵥ x) (plaquette j):=by rw [show L=_ from gradient_s ht x]; unfold vw; rw [cell_origin]; exact one_mul _ -- check
  rw [← he]; let g:=vw p x
  apply Complex.ext
  · change vision L (0,plaquette j)= _; unfold L; rw [see,d_plaquettes]; unfold vision; simp [vw,ht.step,q,Complex.mul_re,cell_origin]; ring
  · change desire L (0,plaquette j)= _; unfold L; rw [believe,d_plaquettes]; unfold desire; simp [vw,ht.step,q,Complex.mul_im,cell_origin]; ring
end YM.QCD.Raft
