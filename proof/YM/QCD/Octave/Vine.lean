import YM.QCD.Octave.Music
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Octave
open Function Filter Set Metric MeasureTheory Lattice Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented
open PhysicalNext.Repeat Lapis Sienna Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Fare Tidings Token Shield Beam Cove Golden NormedSpace
open scoped Topology ENNReal ContDiff BigOperators Classical
open Lat YM.Next.Free Reggae
open Jets.Touch Port Kit Run Stew Bay Strut Leaf Tee Flume Garden Kings Orbit LeafM
open scoped Matrix.Norms.L2Operator
variable {c f:Side}{S:StepData c f} (F:Forest S.ratio){β a b t u v Z w p r:ℝ}{N j l k i d:ℕ}
variable {x:Positions (Uniform.Primary c su) × Poll.Body (Precision.Key F su)}
local notation "X"=>Positions (Uniform.Primary c su) × Poll.Body (Precision.Key F su)
open Revolve
variable {O:Flight j k}(e:f.val=c.val*O.L.val)(T:Grid f→ Sheet f)(W:ℕ → Atom su 2)
open Loom Fleet
variable {A R V s θ c' :ℝ}
open AtomF
-- test Φ all without radius. equality independent of other books.
def mica (N:ℕ) (U:Grid f): EvenA c N:= baker c N (N*(Real.log (T U).det.re-Real.log (T 1).det.re- Extra.Iteration.action W U))+ paleF N (foam O e T U)
local notation "g"=>mica (O:=O) e T W N
abbrev tonic (N:ℕ)(s:ℝ): Grid f→EvenA c N:= wearK c N s ∘ mica (O:=O) e T W N
lemma peaking (h : Species O e V R t a b d T)(U:Grid f): tonic e T W N s U=baker c N (N*(alti f (probe V T W U)- alti f (probe V T W 1))) + powerZ c N s (foam O e T U):=by
    have hp:=freeing h U W; unfold tonic Function.comp mica; simp_rw [← hp,Complex.sub_re,sum_sub_distrib,map_add]; congr 1; change wearK _ _ _ (baker c N _) = baker c N _; rw [gets,show ∀ i:ℝ, wearK c N s (i • 1)=i • wearK c N s 1 from fun i=>map_smul ((wearK c N s).toLinearMap.restrictScalars ℝ) i _,map_one]; rfl
lemma peopled {L J:Type*}[Fintype L][Fintype J][DecidableEq L][DecidableEq J]{x:L→Site f}{y:J→Site f}{Z: Grid f→ArrayL L J}(h:Heritage x y u a i Z A)(ht:0<u): Continuous Z:=by
   obtain ⟨D,E,h⟩:=h; rw [show Z=winch D ∘ Kit.settled from funext fun i=>(h.winched ..).symm]; refine continuous_iff_continuousAt.mpr fun x=> ((h.won _ (citizenship f ht x)).continuousAt).comp ?_; exact (show Continuous (Kit.settled:Grid f→Kit.Pulse f) by unfold Kit.settled; fun_prop).continuousAt -- name
variable (h: Species O e V R t a b d T) (hg:Own f t a i (probe V T W) A) (ht:0<t)(ha:0≤a)(hv:0<s)(hA:0≤A)
local notation "g'"=>tonic e T W N s
include h ht hg
lemma portage : Continuous (g': Grid f→EvenA c N) :=by
   rw [show (g')= _ from funext (peaking e T W h (N:=N) (s:=s))]; exact ((baker c N).continuous.comp (continuous_const.mul (((alti f).continuous.comp (peopled hg ht)).sub continuous_const))).add ((powerZ c N s).continuous.comp (peopled h.soapt ht))
include hv ha hA
def fundsX (w y s A R:ℝ)(N:ℕ):=N*(w*Fintype.card Lat.Fiber*A+w*Fintype.card Lat.Fiber*A)+ s^2*y^2*R
lemma musterX (hy: (Fintype.card (Site f):ℝ)≤ w)(hx:(Fintype.card (Modes c N):ℝ)≤ u)(x:Grid f): ‖g' x‖ ≤ fundsX w u s A R N:=by
   have he: 0≤R:= h.forest.le
   rw [peaking e T W h]; refine (norm_add_le ..).trans (add_le_add ?_ ?_)
   · apply ((baker c N).le_opNorm _).trans; apply (mul_le_of_le_one_left (norm_nonneg _) (colP c N)).trans
     rw [norm_mul,Real.norm_of_nonneg (by positivity : 0 ≤ (N:ℝ))]; apply mul_le_mul_of_nonneg_left _ (by positivity)
     apply (norm_sub_le ..).trans; refine add_le_add ?_ ?_
     all_goals exact ((alti f).le_opNorm _).trans (mul_le_mul ((ascent f).trans (mul_le_mul_of_nonneg_right hy (by positivity))) (hg.value ht ha hA _) (norm_nonneg _) (by have hh := (Nat.cast_nonneg _).trans hy; positivity))
   exact ((powerZ c N s).le_opNorm _).trans (mul_le_mul ((billed hv c N).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hx _) (by positivity))) (h.soapt.value ht ha he _) (norm_nonneg _) (by positivity))
noncomputable abbrev noteC (t b Z:ℝ)(i:ℕ):= clump i ((massQ+massQ)*(1+fabric su i Z)^i) (letterP t i*b)
noncomputable def gross (Z t R A p w a:ℝ)(j N:ℕ):= N*(p*Fintype.card Lat.Fiber* (noteC t A Z j)+p*Fintype.card Lat.Fiber*A)+ (a^2*w^2)*(noteC t R Z j)
lemma conscientious (hp : PaintSupply su l Z)(hy: (Fintype.card (Site f):ℝ)≤ w)(hz: (Fintype.card (Modes c N):ℝ)≤ u)(hx:‖x‖≤1): Brush l (gross Z t R A w u s l N) 1 (g' ∘ projection F) x:=by
   have hh:= tempoP F hp x hx; have hr:= meter F hg ht hA ha hh; have hf:= meter F h.soapt ht h.forest.le ha hh
   have H: ‖alti f‖ ≤ w*Fintype.card Lat.Fiber:= (ascent f).trans (mul_le_mul_of_nonneg_right hy (by positivity)); have hQ : 0 ≤ w:= (Nat.cast_nonneg _).trans hy
   have hv' := (hr.report _ H).separating ((certified (k:=l) (x:=x) zero_le_one _).climb (( (alti f).le_opNorm _).trans
      (mul_le_mul H (hg.value ht ha hA 1) (norm_nonneg _) (by positivity))) le_rfl); have ht := ((hv'.smul (N:ℝ)).report _ (colP c N)); rw [one_mul,Real.norm_of_nonneg (by positivity : 0 ≤ (N:ℝ))] at ht; refine (ht.gathering (hf.report (powerZ c N s) ((billed hv c N).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hz _) (by positivity))))).shimmy (Eventually.of_forall fun i=> peaking e T W h (projection F i))
end YM.QCD.Octave
