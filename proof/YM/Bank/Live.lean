import YM.Bank.Word
import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.TellerFold
import YM.QCD.Flume.Song
/-! Exact Fourier bills at p=0 too. -/
set_option autoImplicit false
noncomputable section
namespace YM.Bank
open Function Lattice Laurent Bloch Precision Matrix Metric Exterior Work.F06
open YM.Next.Free Finset
open Wilson RG AnalyticBridge.LocalGaussianLaws AnalyticBridge.LocalGaussianLaws.Current
open scoped Matrix BigOperators Topology ComplexConjugate InnerProductSpace Matrix.Norms.L2Operator
variable {c f:Side}{k j:ℕ}
open QCD.Flume (twins)

lemma twin_mon (r:Ratio c f)(h:Odd r.count.val)(p:Site c)(l:Site r.count): mon (twins r p l) = aliasAt (mon p) l :=by
    ext1 i; rw [alias_value,mon,QCD.Flume.twin_lift r h]; simp only [Laurent.reciprocal,Pi.smul_apply,
     smul_eq_mul,Pi.add_apply,nsmul_eq_mul, Int.cast_add, Pi.mul_apply, Pi.natCast_apply,
     Int.cast_mul,Int.cast_natCast]; rw [mon]; simp only [Pi.smul_apply,smul_eq_mul,Laurent.reciprocal]
    rw [r.exact_size,Nat.cast_mul]; field_simp [side_ne c,side_ne r.count]
lemma twin_leaf {m:Type}[Fintype m][DecidableEq m] (r:Ratio c f)(h:Odd r.count.val)(p:Site c)(l:Site r.count)(x:Site f)(i j:m): readings r m (x,i) (p,l,j)=rotations f m (x,i) (twins r p l,j):=by rw [sample]; change _=if i=j then mode _ _ else 0; rw [twin_mon r h]

namespace Learn
variable {H:Bed}{a b:ℝ}{m:Type}

def starΔ (H:Bed)(p:Momentum) := signal 1 1 p * spaceK H.metric p
lemma closes_in (hp:Momentum) :  mirage 1 0 hp * live H.metric hp = 0 := by unfold live; simp only [← Matrix.mul_assoc, mirage_chain,Matrix.zero_mul]
lemma closes_out (hp:Momentum) : live H.metric hp * signal 1 0 hp=0 :=by unfold live; rw [Matrix.mul_assoc,signal_chain,Matrix.mul_zero]
lemma houses_c (hp:Momentum) : Commute (gaugeR H.metric hp) (live H.metric hp):= by
    unfold Commute SemiconjBy
    rw [gaugeR,add_mul,mul_add, Matrix.mul_assoc _ (mirage _ _ _) (live _ _), closes_in, Matrix.mul_zero, ← Matrix.mul_assoc (live _ _) (signal 1 0 _), closes_out,Matrix.zero_mul] -- dot
lemma outside : signal 1 1 (0:Momentum)=0:=by unfold signal tripQ wedge; simp [chip]
lemma solves_c (hH:H.metric.safe)(h:Numeric (H.metric.acts c) a b)(he:0<a)(p:Site c):
    starΔ H (mon p)*live H.metric (mon p)=signal 1 1 (mon p):=by
    let q:=mon p; let G:=gaugeR H.metric q; let X:= live H.metric q; let O:= G⁻¹; let A:=signal 1 1 q
    have hx : A*X=A*G:=by
       unfold G gaugeR; rw [Matrix.mul_add,← Matrix.mul_assoc A (signal 1 0 q),show A*signal 1 0 q=0 from signal_chain 1 0 q,Matrix.zero_mul,add_zero]
    change (A*O)*X=A; by_cases hp:q=0
    · have ht:A=0:=by unfold A; rw [hp, outside]
      rw [ht,Matrix.zero_mul,Matrix.zero_mul]
    have hg := purse H.metric h he p hH hp
    have hi : O*X=X*O:= by
       have hf: G*X=X*G:= houses_c q
       have h1: O*G=1:= G.nonsing_inv_mul hg.1; have h2 : G*O=1:= G.mul_nonsing_inv hg.1
       calc
         O*X=O*X*(G*O) := by rw [h2,mul_one]
         _ = X*O:=by rw [← Matrix.mul_assoc,Matrix.mul_assoc O X G,← hf,← Matrix.mul_assoc O,h1,one_mul]
    rw [Matrix.mul_assoc,hi, ← Matrix.mul_assoc,hx,Matrix.mul_assoc, show G*O=1 from G.mul_nonsing_inv hg.1,Matrix.mul_one]
lemma billsT {s:ℕ} (c:Side): Runs (rotations c (TypeFace s)) (rotations c (TypeFace (s+1))) (Exterior.d s c).transpose
   (solo c (mirage 1 s)):=by
     have hg : Runs _ _ _ _ := ((cobound_true s).coarse c).back (rotations_crew _ _) (rotations_crew _ _)
     rw [div_self (stage_ne c),one_smul,solo,fiber_H] at hg
     convert hg
     unfold solo; congr! 2 with i; rw [mirage_herm]; exact real_frequency _ -- try
lemma live_c (c:Side)(hH:H.metric.safe) : Runs (rotations c (TypeFace 1)) (rotations c (TypeFace 1)) (Precision.K (H.metric.acts c)) (solo c (live H.metric)):=by
    unfold Precision.K; have hx:= ((billsT (s:=1) c).product (Corresponds.coarse (R:=H.metric) (F:=H.metric.read) ⟨hH,fun _ _=>rfl⟩ c)).product ((cobound_true 1).coarse c); unfold solo at hx; rw [fiber_mult,fiber_mult] at hx; exact hx
-- use exact Fourier assembly on physical data. Avoid descent rank by using this K-only full-period matrix.
def gaugeΞ (H:Bed)(c:Side) : Matrix (Body 1 c) (Body 1 c) ℂ:= (stageVolume c)⁻¹ • (rotations c (TypeFace 1) * solo c (spaceK H.metric) * (rotations c (TypeFace 1))ᴴ)
def skyF (H:Bed)(k:Momentum):= starΔ H k * mirage 1 1 k
lemma moves (H:Bed)(c:Side): gaugeΞ H c * rotations c (TypeFace 1)=rotations c (TypeFace 1) * solo c (spaceK H.metric) :=by
    unfold gaugeΞ; rw [Matrix.smul_mul]; set Z:= rotations _ (TypeFace 1); rw [Matrix.mul_assoc (_ * _) Zᴴ,show Zᴴ*Z=_ from (rotations_crew _ _).2.2,Matrix.mul_smul,Matrix.mul_one, smul_smul, inv_mul_cancel₀ (stage_ne c), one_smul]
lemma stakes (hH:H.metric.safe)(h: Numeric (H.metric.acts c) a b)(he:0<a) :
     approached (Exterior.d 1 c) * gaugeΞ H c * approached (Precision.K (H.metric.acts c))=approached (Exterior.d 1 c):=by
     apply cancel_rotation c; let F:= rotations c (TypeFace 2); let D:= approached (Exterior.d 1 c); let U:= rotations c (TypeFace 1);
     let g:=gaugeΞ H c; let V:=approached (Precision.K (H.metric.acts c))
     let v:=live H.metric; let A:= signal 1 1
     have ht: V*U=U*solo c v:= live_c c hH; have hp:D* U= F * solo c A:= (cobound_true 1).coarse c
     change D*g*V*U=D*U; rw [Matrix.mul_assoc (D*g), ht, Matrix.mul_assoc D g, ← Matrix.mul_assoc g, moves, Matrix.mul_assoc U,← Matrix.mul_assoc D, hp, Matrix.mul_assoc F]; congr 1;
     unfold solo; simp only [fiber_mult]; have hh(p:Site c): A (mon p)*(spaceK H.metric (mon p)*v (mon p))= A (mon p):= Matrix.mul_assoc .. |>.symm.trans (solves_c hH h he p); simp_rw [hh]
lemma learned_eq (hH:H.metric.safe)(h:Numeric (H.metric.acts c) a b) (he:0<a):
      approached (learned H c)= approached (d 1 c)*gaugeΞ H c * (approached (d 1 c))ᴴ:=by
    let D:= d 1 c; let V:= Precision.K (H.metric.acts c); let Y:= holder D (H.metric.acts c)
    have hp:V*Y= D.transpose:=holder_value D _ ⟨fun x=>(h x).1⟩ he
    change approached (D*Y)=_
    rw [show (approached (d 1 c))ᴴ=approached D.transpose from (prom_adj D).symm,←hp,prom_mul,prom_mul,← Matrix.mul_assoc,stakes hH h he]
lemma learns (hH:H.metric.safe)(h:Numeric (H.metric.acts c) a b)(he:0<a):
     Runs (rotations c (TypeFace 2)) (rotations c (TypeFace 2)) (learned H c) (solo c (skyF H)):=by
    unfold Runs; rw [learned_eq hH h he]; let F:= rotations c (TypeFace 1); let G:= rotations c (TypeFace 2); let D:= approached (d 1 c); let K:=gaugeΞ H c
    have he: Dᴴ*G=F*solo c (mirage 1 1):=by rw [show Dᴴ= approached (d 1 c).transpose from (prom_adj _).symm]; exact billsT c
    have hp : D*F=G*solo c (signal 1 1):= (cobound_true 1).coarse c
    change D*K*Dᴴ*G=G*_
    rw [Matrix.mul_assoc (D*K),he,← Matrix.mul_assoc _ F,Matrix.mul_assoc D, moves,← Matrix.mul_assoc D,hp,Matrix.mul_assoc G, Matrix.mul_assoc G]; unfold solo; simp_rw [fiber_mult]; rfl
end Learn
end YM.Bank
#print axioms YM.Bank.Learn.learns
