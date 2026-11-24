import YM.Siro.Park
import YM.Siro.Step
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Siro
open Function Set Filter Analysis
open Fields (SimpleK)
open Ward (inc)
open scoped Topology NNReal ENNReal InnerProductSpace ContDiff BigOperators
variable {F:Fields}{a b:Axis}{S:F.Kernel}(V:Chamber S a)(H:Brawl S)
variable (p q:F.W)
noncomputable def pairQ(S:F.Kernel)(p q:F.W)(x:E4):= S 2 (points (![0,x])) (![p,q])
include H
lemma duo (x y:E4)(hp:0<x a)(hq:0<y a):inner ℂ (spotR V p x) (spotR V q y)=pairQ S (F.adj a p) q (y-Ortho.move (Signed.reflect a) x) := by
    let z:= Ortho.move (Signed.reflect a) x; let t:= F.adj a p; let u:= points (![z,y]); let v:= (![t,q]); have ht : u∈conf _:=by
             have he:y≠z:= Ward.mirror_ne x y a hp hq; intro i j; fin_cases i <;> fin_cases j<;> simp[u,he,Ne.symm he]
    rw [stamp V _ hp,stamp V _ hq,V.GNS.measure]; change Fields.pointMoment _ [(z,t),(y,q)]=_; rw [show [(z,t),(y,q)]= realize v u from rfl,readAt,← H.translation 2 u ht (-z)]; unfold pairQ; congr 2; apply PiLp.ext; intro i; fin_cases i <;> simp [u,sub_eq_add_neg,z]
include V in
lemma radial (t:ℝ)(ht:0<t):AnalyticAt ℝ (fun s:ℝ=>pairQ S p q (s • basis a)) t:=by
   let k:=t/2; have hk:0<k:=half_pos ht; let v:= k • basis a; let w:= -(k • basis a); have hv : 0<v a:=by simp [v,hk]
   have hu s (h:k<s) : 0< inc a w s a:=by simp[inc,w]; linarith
   have he:= advancing V q w t (hu t (by unfold k; linarith)); let L:= innerSL ℂ (spotR V (F.adj a p) v); apply (((L.restrictScalars ℝ).analyticAt _).comp he).congr
   filter_upwards [lt_mem_nhds (show k<t by unfold k; linarith)] with i hi
   change inner ℂ _ _=pairQ _ _ _ _; rw[duo V H _ _ v _ hv (hu i hi), H.adj_flip]; congr 1; ext j; simp [inc,v,w,Signed.mirrored]; split_ifs <;> simp
-- Gram/transverse
include V in
lemma tickets (x:E4)(hx:0 < x a)(j:b≠a)(f:ℝ→ℂ)(hf:AnalyticAt ℝ f 0)(h:∀ n:ℕ,iteratedDeriv n (fun s:ℝ=> pairQ S (F.adj a p) p ((2*x a) • basis a+s • basis b)) 0=iteratedDeriv n f 0)(t:ℝ): AnalyticAt ℝ (fun s=> spotR V p (inc b x s)) t:=by
    apply Analysis.blossoms _ (shines V H.toSimpleK p j hx) _ f hf _ h; intro u v
    dsimp only; rw [duo V H _ _ _ _ (Ward.step hx _ j) (Ward.step hx _ j)]; congr 1; apply PiLp.ext; intro i; simp [inc,Signed.mirrored]; split_ifs <;> simp_all; ring
variable (b a:Axis)(hv:b≠a)
def spotD(x:E4): Points 2:= points ![0,x]
noncomputable def yawn (a b:Axis):PDE.V →L[ℝ] Points 2:= (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (Points.direction 1 a)+(ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (Points.direction 1 b)
omit H
open Ward (lift)
@[simp]lemma yawn_p (x:PDE.V): yawn a b x=spotD (lift a b x):=by ext k; fin_cases k<;>simp[yawn,spotD,lift,Points.direction]
include hv
lemma town (x:PDE.V)(hp:x∈PDE.side): spotD (lift a b x)∈conf _:=by
     have he:= Ward.ranges a b hp hv; have h: Ward.put a b x ≠ 0:=fun hz=>by rw [hz] at he; exact one_ne_zero (he (a₁:=(1:Fin 2)) (a₂:=0) rfl)
     have ht:lift a b x≠0:=fun ht=> h (by unfold Ward.put; rw [ht]; apply PiLp.ext; intro j; fin_cases j<;>rfl); intro i j; fin_cases i<;>fin_cases j<;>simp[spotD,ht,Ne.symm ht]
include H
variable (u:F.W×F.W)
noncomputable def manyR (S:F.Kernel)(a b:Axis)(p:F.W × F.W)(x:PDE.V):= pairQ S p.1 p.2 (lift a b x)
lemma Qisit : PDE.C (manyR S a b u):=by
     intro z hz; rw [show manyR S a b u= readQ S (![u.1,u.2]) ∘ yawn a b from funext fun i=>by simp; rfl]; apply (discC H _ _).comp _ (yawn a b).contDiff.contDiffAt; rw[yawn_p]; exact town b a hv z hz
noncomputable def astQ(K:Ortho.Skew)(p:F.W×F.W): F.W× F.W:=(F.lie K p.1,p.2)
noncomputable def sctQ(K:Ortho.Skew)(p:F.W×F.W): F.W× F.W:=(p.1,F.lie K p.2)
set_option quotPrecheck false
lemma tangR (x:PDE.V)(hx:x∈PDE.side): PDE.tangent (manyR S a b u) x=x.1 • pairQ S u.1 (F.partialD b u.2) (lift a b x)-x.2 • pairQ S u.1 (F.partialD a u.2) (lift a b x):=by
    let V:= (![u.1,u.2]); let L:=yawn a b; have he(p:PDE.V)(c:Axis)(h:L p=Points.direction 1 c): D p (manyR S a b u) x=pairQ S u.1 (F.partialD c u.2) (lift a b x):=by
           rw [show manyR S a b u= readQ S V ∘ L from funext fun z=>by simp[L]; rfl]; have hw:L x∈conf _:=by rw [show L x= _ from yawn_p ..]; exact town b a hv x hx
           rw[D,fderiv_comp x ((discC H hw _).differentiableAt (by simp)) L.differentiableAt,L.fderiv,ContinuousLinearMap.comp_apply,h]; change D _ _ _= _; rw[fromQ H hw,show L x=_ from yawn_p ..]; unfold readQ pairQ; congr 1; funext i; fin_cases i<;>simp[V]
    unfold PDE.tangent; rw[he _ _ (show L PDE.i=_ from (by simp[L,PDE.i,yawn] : L PDE.i=Points.direction 1 b)), he _ _ (show L PDE.e=Points.direction 1 a from by simp[L,PDE.e,yawn])]
lemma coneR(x:PDE.V)(hx:x∈PDE.side) : let K:= Ortho.plane b a; PDE.law (astQ K) (sctQ K) (manyR S a b) u x= angQ S (![u.1,u.2]) K (spotD (lift a b x)):=by
    intro K; let q:= (![u.1,u.2]); have hp (g:Axis): M4.move K.val ((spotD (lift a b x)) 0) g=0:=by simp[M4.move,spotD]
    have he(v):update q 0 v=![v,u.2]:=by ext1 i; fin_cases i<;>simp [q]
    have hh(v):update q 1 v=![u.1,v]:=by ext1 i; fin_cases i<;>simp [q]
    unfold PDE.law angQ; rw[tangR H _ _ hv u x hx, Fin.sum_univ_two]; dsimp only; dsimp only [q] at he hh; simp_rw [hp,zero_smul,Finset.sum_const_zero, he,hh]; change _= _ +(0:ℂ)+(_+ ∑ i:Axis, M4.move K.val (lift a b x) i • pairQ S _ (F.partialD i u.2) _)
    unfold K; simp_rw [Ward.planeVec a b hv x];
    have hw(f g:Axis→ℂ): (∑ i, if i=a then f i else if i=b then g i else 0)=f a+g b:=by
             have hh i:(if i=a then f i else if i=b then g i else 0)=(if i=a then f i else 0)+(if i=b then g i else 0):=by split_ifs<;> simp_all
             simp_rw [hh,Finset.sum_add_distrib];simp
    simp_rw [ite_smul,zero_smul,neg_smul,hw]; unfold manyR; unfold readQ; simp only[astQ,sctQ, pairQ,spotD, Matrix.cons_val_one,Matrix.cons_val_zero]; abel
lemma primitives (p:F.W×F.W)(n:ℕ)(t:ℝ)(ht:0<t):let K:= Ortho.plane b a; PDE.tower (PDE.law (astQ K) (sctQ K) (manyR S a b) p) n (t,0)=0:=by
    intro K; rw [← PDE.actual (f:=PDE.law _ _ _ p) (PDE.regular _ _ (fun i=> Qisit H _ _ hv i) _ ) (x:=(t,0)) (show _ from ht)]; dsimp only
    let z:= spotD (lift a b (t,0)); have hp(y:ℝ): spotD (lift a b (t,y))=Ward.cast z 1 b y:=by ext i; fin_cases i<;>simp [spotD,lift,z,Ward.cast,Points.direction]
    rw [show (fun y=> PDE.law _ _ _ p (t,y))=angQ S (![p.1,p.2]) K ∘ Ward.cast z 1 b from funext fun y=> (coneR H _ _ hv p (t,y) ht).trans (by rw[hp];rfl)]
    have he:Ward.cast z 1 b 0∈conf _:= by rw [Ward.start]; exact town b a hv _ ht
    refine jet_line H K _ z 1 b 0 he (fun w=>H.line _ w K _ a ?_ he) n; rw[Ward.start]; intro i; fin_cases i; exact ⟨0,by simp [z,spotD]⟩; exact ⟨t,by simp [z,spotD,lift]⟩
end YM.Massive.Siro
#print axioms YM.Massive.Siro.primitives
#print axioms YM.Massive.Siro.tickets
#print axioms YM.Massive.Siro.radial
