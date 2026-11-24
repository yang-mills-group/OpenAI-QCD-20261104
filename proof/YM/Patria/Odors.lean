import YM.Patria.Lawn
import YM.Patria.Motion
import YM.Patria.Scene
/-! Profile symmetry. Twisted placement at translations incl long. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.Massive.Patria.Canvas
open Filter Function Set MeasureTheory Lattice Source RG Wilson Source.Drops
open scoped Matrix.Norms.Frobenius BigOperators Topology Matrix ContDiff Classical
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
variable {B : Type*} {d:ℕ}
open QCD.Revolve TorusPCAC.Geometry Lining Lining.Ferry Lining.Temper
open Poised Beacon Finset
variable (s:Signed)(H:TaperHol){c:Side}(p:EuPin)(b:Cover)(v:ℝ)
lemma perfume (i: Multi d)(x:Cover) : profile (hem s i) (s.act x) v= (marked s i:ℂ)* profile i x v:=by
    have hf: Papyrus.Purl.profileL (hem s i) (s.act x)=marked s i*Papyrus.Purl.profileL i x:=by unfold Papyrus.Purl.profileL; rw [← Equiv.prod_comp s.perm]; unfold marked; rw [← Finset.prod_mul_distrib]; refine Finset.prod_congr rfl (fun j _=>?_); rw [UV.pinned]; unfold Papyrus.Purl.ψ; rw [sign_at,mul_pow,mul_div_assoc]
    rw [Germ.scoutL,Germ.scoutL,hf,borderBuck, Complex.ofReal_mul,mul_left_comm]
-- scalar quote
abbrev airs (H:TaperHol)(c:Side)(x:Cover)(p:Multi d)(v:ℝ):ℂ:= (H.T.χ ((c.val:ℝ)⁻¹ • vector x):ℂ)*ap c x*profile p x v
lemma indeed: Beacon.glow (c:=c) (d:=d) H.T b v=nacre (fun x y=> (spun H.T b x*profile y (offset b x) v) • 1):=by
       ext i j; rw [imprints]; simp only [Beacon.glow,Matrix.of_apply,Matrix.smul_apply,Matrix.one_apply,smul_eq_mul]; by_cases ht:i.2=j.2 <;> by_cases hh:i.1.2=j.1.2 <;> simp [ht,hh]
lemma stillD : Beacon.glow (c:=c) (d:=d) H.T 0 v=nacre (fun x y=> airs H c (Lattice.lift x) y v • 1):=by rw [indeed]; apply congr_arg nacre; funext x y; simp only [spun,airs, offset,map_zero,sub_zero,add_zero] -- remove name
lemma aura_low (x:Cover)(u:Multi d)(h:∀ i,2*(x i).natAbs ≤ c.val+2)(hv:18 ≤ c.val) : airs H c (lift (wrap c x)) u v=airs H c x u v:=by
    by_cases he: lift (wrap c x)=x; · rw [he]
    obtain ⟨i,h1,h2⟩:= boundary x _ rfl h he; have hq (x':Cover)(hX:c.val ≤ 2*(x' i).natAbs+2) : airs H c x' u v=0:=by have hf:= darkness H hv x' i i hX 0 (by norm_num); rw [zero_smul,add_zero] at hf; simp [airs,hf]
    exact (hq _ h2).trans (hq _ (h1.trans (Nat.le_add_right _ 2))).symm -- ambiguous order
lemma tone (x:Site c)(u:Multi d)(he:18 ≤ c.val) : prism s x*airs H c (lift (s.act x)) (hem s u) v = airs H c (lift x) u v*(marked s u:ℂ):=by
     let y:=s.act (lift x); have hh: wrap c y=s.act x:=by unfold y; rw [← wrap_signed,wrap_lift];
     have hz : airs H c (lift (s.act x)) (hem s u) v=airs H c y (hem s u) v:=by
          rw [← hh]; refine aura_low H v y _ (fun i=> ?_) he; obtain ⟨i,rfl⟩:= s.perm.surjective i; unfold y; have h:= lift_centers x i; rw [Signed.act_at]; split <;> omega
     rw [hz]; unfold airs y; rw [perfume,← motion_site,← map_smul,Ortho.motion_at,H.T.even]
     have h: ap c (lift x) * prism s x= ap c (s.act (lift x)):=by simpa [prism, -wrap_signed] using sheet_launch c (lift x) s
     rw [← h]; have hv: prism s x*prism s x=1:= thermal_norm _; let p:= (H.T.χ ((c.val:ℝ)⁻¹ • vector (lift x)):ℂ); calc
        _=(prism s x*prism s x)*(p*ap c (lift x)*profile u (lift x) v*(marked s u:ℂ)):=by ring
        _=_:=by rw [hv,one_mul]
lemma spin_motion (M:Spike)(he:18≤c.val)(hp:p.Lifts s): (Action.moved (F:=6) (n:=c) s M * Beacon.glow H.T 0 v : Matrix (Modes c 6) (SpinMode d) ℂ)=Beacon.glow H.T 0 v * UV.turned (d:=d) p (wave M):=by
   rw [stillD,roller, ink_pin s p hp]
   let Q(i:Multi d) := (marked s i:ℂ) • wave M; let Z(x:Site c)(i:Multi d):Bundle:= airs H c (lift x) i v • 1; let g(x:Site c) := prism s x • wave M
   have ha:= Lining.spar_mul s.act g Z; have hh:= Lining.spar_after (UV.Hem s d) Q Z; refine ha.trans (Eq.trans ?_ hh.symm); unfold Z Q g; apply congr_arg nacre; funext i j; obtain ⟨y,rfl⟩:= (UV.Hem s d).surjective j; rw [Equiv.symm_apply_apply]; simp only [Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one,Matrix.one_mul,smul_smul]
   change (airs H c _ _ v* prism s i) • _= ((marked s y:ℂ)* _) • _; rw [mul_comm, show UV.Hem s d y=hem s y from rfl,tone s H v _ _ he]
   rw [mul_comm]
-- Translation. Full height d
lemma shift_spray (S : Finset Cover)(x: Cover):
        belt c S x * copies 6 (hues (wrap c b) 1 (heat b) 1) = belt c S (x+b):=by
    rw [table,table]; let p:= fun x:Site c=> x+wrap c b; have h : copies 6 (hues (wrap c b) 1 (heat b) 1)=spar p (fun x=>heat b x • 1):=by ext i j; by_cases he:i.2=j.2 <;> by_cases hp:p i.1.1=j.1.1 <;> simp only [p] at * <;> simp [spar_intro,Matrix.blockDiagonal_apply, wave_one,p, copies,hues, rides,shiftE,he,hp, Signed.actEquiv,Signed.act_one] -- shift
    rw [h,spar_spar]; congr 1; · funext i; simp only [p,gain,map_add,add_assoc]
    funext i; rw [Matrix.smul_mul,Matrix.mul_smul, Matrix.one_mul,smul_smul,mul_comm (ap c _),gain,← add_assoc]; exact congr_arg (fun p:ℂ=>p • (1:Bundle)) (heated _ _).symm
lemma stylus (S : Finset Cover)(x: Cover)(p: Cylinder.Formula S 6) : march b (fun U:Grid c=> places x p U) = fun U=>places (x+b) p U:=by
    funext i; have hf:=shift_spray (c:=c) b S x; let V:=copies 6 (hues (wrap c b) 1 (heat b) 1); unfold march post crank places Kit.disguise; dsimp only; rw [show expandAt (wrap c x) (pull 1 (wrap c b) i)= expandAt (wrap c (x+b)) i from (by rw [pull_one]; funext X; simp only [expandAt,Lattice.translate,map_add,add_assoc]), adapt_together]; let Z:=evaluate (expandAt (wrap c (x+b)) i) p
    change adapter (belt c S x*V) (belt c S x* Mstar V) Z= adapter (belt c S (x+b)) (belt c S (x+b)) Z; rw [show belt c S x*V=_ from hf,← belt_star c S x,← mstar_mul, show belt c S x*V=_ from hf,belt_star]
end YM.Massive.Patria.Canvas
#print axioms YM.Massive.Patria.Canvas.tone
#print axioms YM.Massive.Patria.Canvas.stylus
