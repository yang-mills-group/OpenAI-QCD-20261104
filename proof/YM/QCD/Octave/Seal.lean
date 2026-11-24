import YM.QCD.Octave.Pact
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
open Quarry Stationary Sparks Eyrie Raft Smoke
variable {ξ ξ' a' C C' t' ψ hv r' A' :ℝ}{h:f.val=c.val*O.L.val} {P:Plan j} (J:Offer 1 p C) (Q:Offer 2 r C')
local notation "V'"=>Stationary.input su f
lemma ink_multiply {E I J K:Type}[NormedAddCommGroup E][NormedSpace ℝ E][Fintype I][Fintype J][Fintype K][DecidableEq I][DecidableEq J][DecidableEq K]{Z:E→Matrix I J ℂ}{Y:E→Matrix J K ℂ}{x:E}(h:ContDiffAt ℝ ω Z x)(hp:ContDiffAt ℝ ω Y x):ContDiffAt ℝ ω (fun i=>Z i*Y i) x:=matrix_g fun i j=>ContDiffAt.sum (s:=Finset.univ) (fun l _=>(smear h i l).mul (smear hp l j))
lemma ink_star {E I J:Type}[NormedAddCommGroup E][NormedSpace ℝ E][Fintype I][Fintype J][DecidableEq I][DecidableEq J]{Z:E→Matrix I J ℂ}{x:E}(h:ContDiffAt ℝ ω Z x):ContDiffAt ℝ ω (fun i=>(Z i)ᴴ) x:=matrix_g fun i j=>(starL ℝ (A:=ℂ)).contDiff.contDiffAt.comp x (smear h j i)
lemma leg {J K:Type}[Fintype J][Fintype K][DecidableEq J][DecidableEq K]{u:J→Site f}{v:K→Site f}{T:Grid f→ArrayL J K}(h:Heritage u v t p i T b)(ht:0<t): ContDiffAt ℝ ω (T ∘ Stationary.input su f) 0:=by
   obtain ⟨Dq,Y,h⟩:=h -- notation
   let g:= Kit.settled ∘ V'
   have he: AnalyticAt ℂ (winch Dq) (g 0):=PolyDisc.finiteD _ (_root_.mem_nhds_iff.mpr ?_) -- predicate h.won
   rotate_left
   · exact ⟨Kingdom f t,h.won,country f _,citizenship f ht _⟩
   exact ((he.contDiffAt.restrict_scalars ℝ).comp 0 (pulse_flow f).contDiffAt).congr_of_eventuallyEq (Eventually.of_forall fun i=>(h.winched _).symm)
local notation "U"=> park O h P J Q ξ u
local notation "W'"=>park O h P J Q ξ' u
lemma roomP (hs:Species O h V R t a b d T)(hr:0<t) : ContDiffAt ℝ ω (T ∘ Stationary.input su f) 0 ∧ ContDiffAt ℝ ω (tied O h 0 ∘ Stationary.input su f) 0:=by
   let F₀:= T ∘ V'; let G:= inverser T ∘ V'
   have hx:= inverse_ink (leg hs.hashed hr) (show IsUnit (G 0).det from ?_); rotate_left
   · change IsUnit ((T _)⁻¹.det); rw [Matrix.det_nonsing_inv,Ring.inverse_eq_inv]; exact isUnit_iff_ne_zero.mpr (inv_ne_zero (hs.sole _|>.ne_zero))
   constructor
   · apply hx.congr_of_eventuallyEq; exact Eventually.of_forall fun i=>Eq.symm (Matrix.nonsing_inv_nonsing_inv (T _) (hs.sole _))
   have he: ContDiffAt ℝ ω F₀ 0:= hx.congr_of_eventuallyEq (Eventually.of_forall fun i=>Eq.symm (Matrix.nonsing_inv_nonsing_inv (T _) (hs.sole _)))
   let q:= tied O h 0 ∘ V'; let f':= leftL O h T ∘ V'
   have hz:(∀ i, f' i * F₀ i=q i):=by intro i; change _*_*_=q i; rw [Matrix.mul_assoc,show inverser T _* _= _ from ?_, Matrix.mul_one]; rfl; exact Matrix.nonsing_inv_mul _ (hs.sole _)
   exact (ink_multiply (leg hs.links hr) he).congr_of_eventuallyEq (Eventually.of_forall fun i=> (hz _).symm)
variable (hp:0<p)(hr:0<r)(ht:0<t)(he:Species O h V R t a b d (park O h P J Q ξ u)) (hζ:0<ξ) (hξ: ξ≤1)
    (hw:Species O h V R t' a b d (park O h P J Q ξ' u))(ht':0<t')(hζ':0<ξ')(hξ':ξ'≤1)
include hp hr ht he hζ hξ hζ' hξ'
lemma resonate : Eyrie.Duet (U ∘ V') (W' ∘ V'):=by
   let Z t:= castF (blossomT J Q t f); have hz:= Raft.sessionD (Tee.kinder J Q (n:=f) hp hr hζ hξ); have hh := Raft.sessionD (Tee.kinder J Q (n:=f) hp hr hζ' hξ')
   let f:= (U ∘ V')- Z ξ
   have hf: ContDiffAt ℝ ω f 0:= (roomP _ he ht).1.sub hz.leftF
   have hx i:f+Z i = park O h P J Q i u ∘ V':=funext fun v=>by unfold f Z park; simp only [Function.comp_apply,castF, Pi.add_apply,pesto,trunkM, Pi.sub_apply]; change _=_; abel
   rw [← hx,← hx]; exact (Eyrie.Duet.together hf EventuallyEq.rfl).add (hz.chain hh.flip)
include hw ht'
set_option maxHeartbeats 600000 in
lemma truce (hB:Own f t a i (probe V (U) W) A) : Eyrie.Duet (tonic h (U) W N s ∘ V') (tonic h (W') W N s ∘ V'):=by
   let u:= (U) ∘ V'; let v':=(W') ∘ V'; have hp := resonate J Q hp hr ht he hζ hξ hζ' hξ'
   have hz : Eyrie.Duet (logs V (U) ∘ V') (logs V (W') ∘ V'):=by
      let F (x: Sheet f):= lap (Cost.notch V x); have hQ: ‖Cost.notch V (u 0)‖ <1:= he.pupils _
      exact duchy F hp ((Smoke.lit hQ).1.comp _ (contDiffAt_const.sub (contDiffAt_id.const_smul (V:ℂ)))) -- notch i
   let q₀:= probe V (U) W; let q':=probe V (W') W
   have hf:Eyrie.Duet (q₀ ∘ V') (q' ∘ V'):=by
      let g : Cnr f → Sheet f := -robe W ∘ V'; have hg:g=q₀ ∘ V' - logs V (U) ∘ V' :=funext fun i=> by simp only [g,q₀,Function.comp_apply,Port.probe,Pi.neg_apply,Pi.sub_apply]; abel
      have he: ContDiffAt ℝ ω g 0:=by rw [hg]; exact (leg hB ht).sub hz.leftF
      have hp:= hz.add (Eyrie.Duet.together he EventuallyEq.rfl); simp_rw [show logs V U ∘ V' + g=q₀ ∘ V' from funext fun i=> Eq.symm (sub_eq_add_neg _ _), show logs V W' ∘ V'+g=q'∘V' from funext fun i=> Eq.symm (sub_eq_add_neg _ _)] at hp; exact hp
   have hg: q₀ 1=q' 1:=by have hp:= hf.meet; simpa only [Function.comp_apply, input_zero] using hp
   let L:= tied O h 0 ∘ V'; let F₀:= powerZ c N s ∘ foam O h (U) ∘ V'
   have hZ: Eyrie.Duet F₀ (powerZ c N s ∘ foam O h (W') ∘ V'):=by
       let g:= fun x:Sheet f × Matrix (Row c) (Row f) ℂ=>powerZ c N s (1-x.2*x.1⁻¹*x.2ᴴ)
       let a x:=(u x,L x); let w x:=(v' x,L x); have he':ContDiffAt ℝ ω g (a 0):= by
          apply (powerZ c N s).contDiff.contDiffAt.comp _ (f:=fun x:Sheet f × Matrix (Row c) (Row f) ℂ=>1-x.2*x.1⁻¹*x.2ᴴ); refine contDiffAt_const.sub ?_; let x:=a 0; have hm:ContDiffAt ℝ ω (fun w:Sheet f × Matrix (Row c) (Row f) ℂ=> w.1⁻¹) x:=inverse_ink contDiffAt_fst (show IsUnit (u 0).det from he.sole _)
          exact ink_multiply (ink_multiply contDiffAt_snd hm) (ink_star contDiffAt_snd)
       have hg:Eyrie.Duet a w:=paired hp (Eyrie.Duet.together (show ContDiffAt ℝ ω L 0 from (roomP _ he ht).2) EventuallyEq.rfl); change Eyrie.Duet (g ∘ a) (g ∘ w); exact duchy g hg he'
   let g (x:Sheet f):=baker c N (N*(alti _ x-alti _ (q₀ 1))); have he':ContDiff ℝ ω g:=by unfold g; fun_prop
   have ht':= (duchy g hf he'.contDiffAt).add hZ; refine ?_; rw [show tonic h U W N s= _ from funext (peaking _ _ W he),show tonic h W' W N s= _ from funext (peaking _ _ W hw),show probe V (W') W 1=q₀ 1 from hg.symm]; exact ht'
end YM.QCD.Octave
