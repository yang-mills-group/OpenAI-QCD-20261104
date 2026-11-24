import YM.QCD.Stew.Tally
/-! # relevant coordinates as real linear averages. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Stew
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N:ℕ} {v:Strut c}{k:Spike}{g:Site c→ℂ} {w r a u:ℝ}{p:BudgetPoint}
open Revolve Flume Quarry AnalyticBridge.VerifiedReset
variable {ι β:Type}(E:Gem c N ι)
-- coefficient mass and wave slot sum functional. preExponent later.
structure Crossing (E:Gem c N ι) where
 blank : Dyed E
 rays (s:Strut c)(k:Spike)(d:Site c→ℂ): Warrant s d k→∃ e:Equiv.Perm ι,∀ i,E.addr (e i)=rotateL (E.addr i) s ∧ ∀ U, Diode N s k d (E.view i (sky s U))= E.view (e i) U
variable (b:Flavor N)
def mote (b:Flavor N)(p:RegularAddress c)(x: Grid c→EvenA c N)(z:SampleX):Spike:=if Nonwrapping p.support p.site then shape p.site (feeF b (x 1)) z else 0
def lane (i : ι):= mote b (E.addr i) (E.view i)
def unitM (o: Site c)(x:SampleX)(i:ι): Spike:= if o=(E.addr i).site then lane E b i x else 0
def till (o:Site c)(s:SampleX):Spike:= ∑' i,unitM E b o s i
def tale (M:Spike): Spike := g5*star M*g5
lemma headQ (X: RegularAddress c)(y: Grid c→EvenA c N)(x:SampleX) (hh:Fit (y 1))(hC: shadeG y)(hp:Regal c N (y 1)=y 1): mote b X y (invert x)=tale (mote b X y x):=by unfold mote; split; exact starM b y hh hC hp x _; simp [tale]
lemma stretch (u:Strut c)(X: RegularAddress c): Nonwrapping (rotateL X u).support (rotateL X u).site↔ Nonwrapping X.support X.site:= by exact nonwrapping_turn ..
lemma whirl (i:RegularAddress c)(x z: Grid c→ EvenA c N)(d:SampleX)(hp:Warrant v g k)(he: Fit (x 1))(hZ: ∀ V, Diode N v k g (x (sky v V))=z V)(hv : shadeG x)(h:Gated i.support (x 1)): mote b (rotateL i v) z (tide v.1 d)=skySig v.1 d •(k*mote b i x d*star k):=by
   unfold mote; by_cases hk: Nonwrapping i.support i.site
   · rw [if_pos hk,if_pos ((stretch v i).2 hk),← hZ,show sky v 1=1 from ?_]
     · exact pos_h b x he hv d hp _ _ hk h
     ext1 i; simp [Strut.sky,pull,Step.read]
   rw [if_neg hk,if_neg (mt (stretch v i).1 hk),mul_zero,zero_mul,smul_zero]
lemma costsE {f:ι→ℝ} (hw: Summable f)(he:0 < w)(hp : ∀ i, Sen (E.addr i).site w (E.view i 1)≤ f i)(s:SampleX): Summable fun i=> ‖lane E b i s‖:=by
    obtain ⟨p,hP,H⟩:=preMoment; apply ((hw.mul_left p).mul_right ((w^2)⁻¹)).of_nonneg_of_le (fun _=> norm_nonneg _) (fun i=>?_)
    unfold lane mote; split; swap; · rw [norm_zero]; have hP' : 0 ≤ f i:=(norm_nonneg _).trans (hp i); positivity
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm]; exact (H _ _ b _ _ _ _ he.le).trans (mul_le_mul_of_nonneg_left (hp i) (zero_le_one.trans hP))
-- no placeholder flow, direct Summable
variable (he:E.Gather)(hp:Crossing E)(hv:∀ i:SampleX,Summable fun j=> ‖lane E b j i‖)
lemma concession {i:SampleX} (hx: Summable fun j=> ‖lane E b j i‖) (o:Site c) : Summable (unitM E b o i):=by
   apply Summable.of_norm_bounded hx; intro j; unfold unitM; split; exact le_rfl; rw [norm_zero]; exact norm_nonneg _
include he hp hv
lemma seeding (i:SampleX)(o : Site c)(hp':Warrant v g k): till E b (act v o) (tide v.1 i)=skySig v.1 i •(k*till E b o i*star k):=by
   obtain ⟨e,hF⟩:=hp.rays v k g hp'; unfold till; rw [← e.tsum_eq]; have hf:=concession E b (hv i) o
   have hx j: unitM E b (act v o) (tide v.1 i) (e j)=skySig v.1 i • (k*unitM E b o i j*star k):=by
      obtain ⟨hZ,hM⟩:=hF j
      unfold unitM lane; rw [hZ]; by_cases hz:o=(E.addr j).site
      · rw [if_pos hz,if_pos (show _= (rotateL ..).site from congr_arg (act v) hz)]; exact Stew.whirl b (E.addr j) (E.view j) _ i hp' (hp.blank.num j 1) hM (hp.blank.gauge j) (he.role ..)
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
    have ht j: unitM E b 0 (invert i) j=g5*star (unitM E b 0 i j)*g5:=by unfold unitM; split; exact headQ b _ _ i (hp.blank.num j _) (hp.blank.gauge _) (hp.blank.real j _); simp
    simp_rw [ht]; rw [Summable.tsum_mul_right, Summable.tsum_mul_left, tsum_star]
    · exact hf.star
    exact hf.star.mul_left _
end YM.QCD.Stew
