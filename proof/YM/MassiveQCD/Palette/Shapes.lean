import YM.MassiveQCD.Palette.Phased
import YM.QCD.Stew.Rally
/-! # stencil permutation for signed frames. Keep chart parity at winding -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Stew.Phased
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N:ℕ} {v:Strut c}{k:Spike}{g:Site c→ℂ}
open Revolve Flume Quarry AnalyticBridge.VerifiedReset

lemma known (x:Grid c→ EvenA c N)(h:shadeG x)(hp:AccentFit (x 1))(b: Flavor N)(i j:Site c) : cell (feeF b (x 1)) i j=wave (blot b (x 1) i j):=by
   apply gilt; intro k
   let p: Frame c:=fun _=>k; have hx : gauge p (1:Grid c)=1:=by ext1 e; simp [p,Lattice.gauge]
   let v:=x 1; have hV: sways (Lat.copies N (siteRot p)) v=v:=by apply Subtype.ext; have he:= h 1 p; rw [hx] at he; exact he
   let M:=feeF b v; let Q:= siteRot p; have hr : M=star Q*M*Q:=by exact (congr_arg (feeF b) hV.symm).trans (rite v b _ hp)
   have hG : Q*M=M*Q:=by nth_rw 1 [hr]; rw [← Matrix.mul_assoc,← Matrix.mul_assoc,(siteRot_u p).2, one_mul]
   have hv₁(Y: Site c→Bundle)(U:Sheet c): cell (U* rides (Equiv.refl _) Y) i j=cell U i j *Y j:=by
       nth_rw 1 [← star_star (rides (Equiv.refl _) Y)]; rw [ride_ad, cell_ride_right, star_star]; rfl
   have hm:=congr_arg (fun X=>cell X i j) hG; unfold Q siteRot at hm; rw [cell_ride_left,hv₁] at hm; exact hm
lemma realK {x:Grid c→EvenA c N}(b:Flavor N)(h1:AccentFit (x 1))(h:shadeG x)(he:Regal c N (x 1)=x 1)(i j:Site c): blot b (x 1) i j=g5*star (blot b (x 1) j i)*g5:=by
   let A:=feeF b (x 1); let Γ:=chirality c; have hG: A=star Γ*star A*Γ:= by have hp:=Phased.burst (x 1) b h1; rw [he] at hp; exact hp
   have hk : cell A i j=wave (g5*star (blot b (x 1) j i)*g5):=by
      rw [hG]; rw [show Γ=star (rides (Equiv.refl (Site c)) (fun _=>J0)) from chi_star.symm,star_star,cell_ride_right,cell_ride_left,Equiv.refl_apply,Equiv.refl_apply, show cell (star A) i j=star (cell A j i) from cell_flip ..]; rw [show cell A j i=wave _ from known x h h1 b j i,wave_star, cT]; simp only [J0,wave_mul]
   exact congr_arg gold hk|>.trans (leafy _)
lemma rollsL {x: Grid c→EvenA c N}(hp:Warrant v g k)(h:AccentFit (x 1))(hf:shadeG x)(i j:Site c)(b:Flavor N):
    blot b (Diode N v k g (x 1)) (act v i) (act v j)=(g i*g j) • (k*blot b (x 1) i j*star k):=by
   unfold blot; rw [show feeF b (Diode N v k g (x 1))=_ from rite _ _ _ h]; change gold (cell (star (rides (act v) (lightP v k g))*feeF b (x 1)*rides (act v) (lightP v k g)) _ _)=_; rw [billsL,known x hf h b i j]; unfold lightP; simp only [star_smul,Matrix.smul_mul, Matrix.mul_smul,wave_star,star_star,wave_mul, smul_smul]
   obtain hx|hx:= hp.1.sign i <;> obtain hj|hj:=hp.1.sign j <;> simp only [hx,hj,star_one,star_neg,one_mul,neg_mul, neg_neg, mul_one, neg_smul,one_smul,← wave_neg,leafy]
lemma pos_h (b: Flavor N)(x:Grid c→EvenA c N)(h:AccentFit (x 1))(hf:shadeG x)(p:SampleX)(hp:Warrant v g k)(D:Support c)(o)(he:Nonwrapping D o)(hv:Gated D (x 1)):
    shape (act v o) (feeF b (Diode N v k g (x 1))) (tide v.1 p)=skySig v.1 p • (k*shape o (feeF b (x 1)) p*star k):=by
    let T:=D.image (act v); rw [sluice _ b _ T _ (gateS _ _ _ _ _ hv),sluice _ b _ D _ hv]
    unfold T; rw [sum_image (act v).injective.injOn]; simp only [Finset.smul_sum, Matrix.sum_mul,Matrix.mul_sum,Finset.smul_sum]; refine sum_congr rfl (fun i hi=>?_); rw [sum_image (act v).injective.injOn]; refine sum_congr rfl fun j hj=>?_ ; rw [rollsL hp h hf, Matrix.mul_smul] -- order
    simp_rw [Matrix.smul_mul, smul_smul]; congr 1; rw [tideM v o i j p (he i hi) (he j hj),← booth hp o i j (he i hi) (he j hj)]; ring
lemma starM (b:Flavor N)(x:Grid c→EvenA c N)(h: AccentFit (x 1))(hf: shadeG x)(hr: Regal c N (x 1)=x 1)(p:SampleX)(o): shape o (feeF b (x 1)) (invert p)=g5*star (shape o (feeF b (x 1)) p)*g5:=by
   unfold shape; simp only [star_sum, Matrix.sum_mul, Matrix.mul_sum]; rw [sum_comm]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _
   change _ • blot b (x 1) _ _ =g5*star (_ • blot b (x 1) _ _) * _
   rw [star_smul,Matrix.mul_smul, Matrix.smul_mul]; apply congr_arg₂ (· • ·)
   · simp only [star_mul,realSS,g_mark]; rw [mul_comm]; unfold mark invert; cases p; rfl; next p=> rcases p with ⟨i,_|_⟩ <;> rfl
   apply realK b h hf hr
variable {ι β:Type}(E:Gem c N ι)(b:Flavor N)
lemma headQ (X: RegularAddress c)(y: Grid c→EvenA c N)(x:SampleX) (hh:AccentFit (y 1))(hC: shadeG y)(hp:Regal c N (y 1)=y 1): mote b X y (invert x)=tale (mote b X y x):=by unfold mote; split; exact starM b y hh hC hp x _; simp [tale]
lemma whirl (i:RegularAddress c)(x z: Grid c→ EvenA c N)(d:SampleX)(hp:Warrant v g k)(he: AccentFit (x 1))(hZ: ∀ V, Diode N v k g (x (sky v V))=z V)(hv : shadeG x)(h:Gated i.support (x 1)): mote b (rotateL i v) z (tide v.1 d)=skySig v.1 d •(k*mote b i x d*star k):=by
   unfold mote; by_cases hk: Nonwrapping i.support i.site
   · rw [if_pos hk,if_pos ((stretch v i).2 hk),← hZ,show sky v 1=1 from ?_]
     · exact pos_h b x he hv d hp _ _ hk h
     ext1 i; simp [Strut.sky,pull,Step.read]
   rw [if_neg hk,if_neg (mt (stretch v i).1 hk),mul_zero,zero_mul,smul_zero]
variable (he:E.Gather)(hp:Keyed E)(hv:∀ i:SampleX,Summable fun j=> ‖lane E b j i‖)
include he hp hv
lemma seeding (i:SampleX)(o : Site c)(hp':Warrant v g k): till E b (act v o) (tide v.1 i)=skySig v.1 i •(k*till E b o i*star k):=by
   obtain ⟨e,hF⟩:=hp.turns v k g hp'; unfold till; rw [← e.tsum_eq]; have hf:=concession E b (hv i) o
   have hx j: unitM E b (act v o) (tide v.1 i) (e j)=skySig v.1 i • (k*unitM E b o i j*star k):=by
      obtain ⟨hZ,hM⟩:=hF j
      unfold unitM lane; rw [hZ]; by_cases hz:o=(E.addr j).site
      · rw [if_pos hz,if_pos (show _= (rotateL ..).site from congr_arg (act v) hz)]; exact Phased.whirl b (E.addr j) (E.view j) _ i hp' (hp.notes.num j 1) hM (hp.notes.gauge j) (he.role ..)
      rw [if_neg hz,if_neg (show ¬ _=(rotateL (E.addr j) v).site from (act v).injective.ne hz),mul_zero,zero_mul,smul_zero]
   simp_rw [hx]; exact (((hf.hasSum.mul_left k).mul_right (star k)).const_smul _).tsum_eq
lemma plums (i : Site c): till E b i=till E b 0:=by
    let V:Strut c:=(1,i); obtain ⟨p,hp'⟩:= Revolve.shades 1 (0:Site c) 0 i
    have hh: Warrant V p 1:=⟨hp',Swing.none⟩
    funext x; have hv':= seeding E b he hp hv x 0 hh; rw [star_one, one_mul,mul_one,show skySig V.1 x=1 from ?_,one_smul, show act V 0=i from ?_,show tide V.1 x=x from ?_] at hv'; exact hv'
    · rcases x with _|x <;> rfl
    · change affine 1 i 0=i; simp [affine]
    cases x<;> rfl -- ordering swap inspect
lemma portraits : Poem (till E b 0):=by
    refine ⟨?_,?_⟩
    · intro p s k h; let u:Strut c:=(s,0); obtain ⟨g,hg⟩:= shades s (0:Site c) 0 0; have hx:act u 0=0:=by change affine s (0:Site c) 0=0; simp [affine]
      have hv':=seeding E b he hp hv p 0 (show Warrant u g k from ⟨hg,h⟩); rw [hx] at hv'; exact hv'
    intro i; unfold till; have hf:=concession E b (hv i) 0
    have ht j: unitM E b 0 (invert i) j=g5*star (unitM E b 0 i j)*g5:=by unfold unitM; split; exact headQ b _ _ i (hp.notes.num j _) (hp.notes.gauge _) (hp.notes.real j _); simp
    simp_rw [ht]; rw [Summable.tsum_mul_right, Summable.tsum_mul_left, tsum_star]
    · exact hf.star
    exact hf.star.mul_left _
end YM.QCD.Stew.Phased
