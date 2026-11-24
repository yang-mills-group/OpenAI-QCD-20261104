import YM.Siro.Servo
set_option maxHeartbeats 440000
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Siro
open Function Set Filter Analysis
open Ward (inc)
open Fields (SimpleK)
open scoped Topology NNReal ENNReal InnerProductSpace ContDiff BigOperators
variable {F:Fields}{a b:Axis}{S:F.Kernel}(V:Chamber S a)(H:Brawl S)
include H
lemma cared (p:F.W)(x:E4)(hx:0<x a)(j:b≠a)(t:ℝ):AnalyticAt ℝ (fun s=> spotR V p (inc b x s)) t:=by
  let A:= F.adj a p; let y:=2*x a; have hy:0<y:=by unfold y; positivity
  obtain ⟨d,hd,hA⟩:= H.high A; obtain ⟨e,he,hp⟩:= H.high p
  let z:PDE.V:=(y,0); let K:= Ortho.plane b a; let u:↥(F.level d)× ↥(F.level e):= (⟨A,hA⟩,⟨p,hp⟩); have hz:= ann_at V H hd he K u z (show _ from hy);
  apply tickets V H p x hx j (fun t=>ann H hd he K u a (y,t)) (by exact hz.comp (f:=fun t=>(y,t)) (ContDiffAt.analyticAt (contDiffAt_const.prodMk contDiffAt_id))) _ t
  let R(p):= ann H hd he K p a; let I(i:↥(F.level d)×↥(F.level e)) : F.W× F.W:= (i.1.val,i.2.val); let G(i):=manyR S a b (I i); let L(i)x:= G i x-R i x; have hR i: PDE.C (R i):= fun p hx=>(ann_at V H hd he K _ p hx).contDiffAt
  have hG i : PDE.C (G i):= Qisit H b a j _
  let l(i:↥(F.level d) × ↥(F.level e)):= rising H hd K i; let r(i:↥(F.level d) × ↥(F.level e)):= rising' H he K i
  have ht :∀ i n t,0<t → PDE.tower (PDE.law l r L i) n (t,0)=0:=by
      intro i n t h; have hq : EqOn (PDE.law l r L i) (PDE.law l r G i) PDE.side:= fun x hx=> (PDE.linear l r hG hR i hx).symm.trans (by rw [show PDE.law l r R i x=0 from settles V H hd he K i x hx, sub_zero]); exact (PDE.vanishing hq n (show (t,0)∈ PDE.side from h)).trans (primitives H b a j (I i) n _ h) -- defeq?
  have hm(i) (t:ℝ)(ht:0<t):L i (t,0)=0:=by unfold L; apply sub_eq_zero.mpr; unfold G manyR R ann; simp [baseK, Ward.Circle.θ,Ward.Circle.r,ht.le,Ward.lift]; rfl
  intro n; have hg:=PDE.sure l r (fun i=> PDE.C.diff (hG i) (hR i)) ht hm n y hy u
  have hs:= PDE.diffJet (hG u) (hR u) n (show z∈PDE.side from hy); have hh : PDE.tower (G u) n z=PDE.tower (R u) n z := sub_eq_zero.mp (hs.symm.trans hg)
  exact (PDE.actual (hG u) (x:=z) hy n).trans (hh.trans (PDE.actual (hR u) hy n).symm)
end YM.Massive.Siro
#print axioms YM.Massive.Siro.cared
