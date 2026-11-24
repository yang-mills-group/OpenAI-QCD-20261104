import YM.Massive.Pith.Knob
import YM.Massive.Pith.Monitor
import YM.QCD.Finch.Trust
/-! # extracting. The flavor/mud shelf issued onto just the original support. We have to use the OLD anchor, especially on wrapped tests. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false -- parallel unfold cases
noncomputable section
namespace YM.QCD.Pith
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron
open Revolve Stew Reggae Brick Port Entr
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N:ℕ} {v:Strut c}{k:Spike}{g:Site c→ℂ}
variable (b:Flavor N)
local notation "J"=> Modes c N
variable {t r q:ℝ}{p:BudgetPoint}{ι α β:Type}
variable (o:Site c) (M:Spike)
def selectF (c:Side) (b:Flavor N): EvenA c N→L[ℂ]EvenA c N:= LinearMap.toContinuousLinearMap { toFun:=knob c b, map_add':=fun _ _=>map_add .., map_smul':=fun x y=>complexFactor x (idP b) y}
def loanP (b:Flavor N)(o:Site c): Spike→L[ℂ]EvenA c N:=(selectF c b).comp ((nozzle c N).comp (pillar o none 1))
def lightP1 (b:Flavor N)(o:Site c)(M:Spike):EvenA c N:= loanP b o M
lemma Lform : lightP1 b o M=knob c b (Port.paleF N (localX o M)):=rfl
lemma credential (i:Flavor N): feeF i (lightP1 b o M)=if b=i then localX o M else 0:=profileK ..
lemma mudLoan : mud (lightP1 b o M)=0:= (walks ..).trans (form_card ..)
lemma phaseLoan : Phases (lightP1 b o M):= finance b _ (fitP _ (form_fit (localX o M) N))
lemma Regal_loan (h:M=Stew.tale M):Regal c N (lightP1 b o M)=(lightP1 b o M):=by
    have he:localX o M=foldH (localX o M):= by change _= Lat.chirality c * star _ * Lat.chirality c; rw [localStar,latC, rentsL,rent_rev]; exact congr_arg (localX o) h
    rw [Lform,← songP b, dusted c N _ he]
where latC: Lat.chirality c= onSpin c g5 := rfl
lemma shadeLoan : shadeG (fun _:Grid c=>lightP1 b o M):=by
    intro U k; let B:=siteRot k; have he: sways (copies N B) (paleF N (localX o M))=paleF N (localX o M):=Port.rayTrade (Lat.copies N B) (copies_unitary _ _ (siteRot_u k)) (localX o M) (localX o M) (by rw [← copies_star,← Lat.copies_mul,← Lat.copies_mul];apply congr_arg; rw [show B * _=_ from (commG o M k).eq,Matrix.mul_assoc,(siteRot_u k).2,mul_one]); exact congr_arg Subtype.val ((vow b _ B).symm.trans (congr_arg _ he))
lemma GateLoan (Y:Support c) (h:o∈Y): Gated Y (lightP1 b o M) := by apply carriesP; change Gated Y (paleF N (localX o M)); rw [siteBl]; exact padBl _ _ _ h h
-- Woven slice price
open Jets.Sun
abbrev priceP (N:ℕ):=9*fingers N^2*‖goldW‖
lemma priceP_nonneg : 0 ≤ priceP N:=by unfold priceP; positivity
lemma priceLoan (h:0<t):Sen o t (lightP1 b o M) ≤priceP N*(t^2*‖M‖):=(wagesP b (paleF N (localX o M)) o h.le).trans (boardFee h M N)
lemma constWoven (X:Support c)(o:Site c)(x:EvenA c N)(ht:Gated X x)(hp:Sen o t x ≤ r): Woven o X p t (fun _=> x) r :=by
    have h:0≤r:= (norm_nonneg _).trans hp
    refine ⟨fun _ _ _=> rfl,fun _=>ht,fun _ _=>contDiffAt_const,?_,measurable_const,h⟩
    intro i hi l hh he; cases l with
    | nil=> exact hp
    | cons i l=> rw [Work.G07.left_const,if_neg (by simp),← measures,map_zero,norm_zero]; exact h
lemma costLoan (Y:Support c) (h:o∈Y)(hp:0<t): Woven o Y p t (fun _=>lightP1 b o M) (priceP N*(t^2*‖M‖)):=constWoven _ _ _ (GateLoan b o M Y h) (priceLoan b o M hp)
lemma turnLoan (h:Warrant v g k) : Diode N v k g (lightP1 b o M) = lightP1 b (act v o) (k*M*star k):=by
    change sways (copies N (haze v k g)) (knob c b _)=_ ; rw [←vow]; refine congr_arg (knob c b) ?_
    let H:= haze v k g; apply rayTrade _ (copies_unitary _ _ (trail h)); rw [← copies_star,← Lat.copies_mul,← Lat.copies_mul]; apply congr_arg; change localX o M= haze v k g*localX (act v o) (k*M*star k)* _;rw [← principal o M h, Matrix.mul_assoc,(trail h).2,mul_one]

variable (E:Gem c N ι)(i:ι)
def lampShelf : EvenA c N:=∑ b: Flavor N,lightP1 b (E.addr i).site (lane E b i none)
def sewShelf := Reggae.ocean c N (Reggae.river c N (E.view i 1))
def tallyShelf : EvenA c N:= sewShelf E i+lampShelf E i
lemma frameShelf (Y:Support c)(h:(E.addr i).site ∈Y) : Gated Y (lampShelf E i):=by unfold Gated lampShelf; rw [map_sum]; exact Subalgebra.sum_mem _ fun j _=> GateLoan j _ _ Y h
lemma chartShelf : shape (E.addr i).site (feeF b (lampShelf E i)) none=lane E b i none:=by
    change profile _ none (meter b _)=_; unfold lampShelf; rw [map_sum,sum_eq_single b]; · change shape _ (feeF _ _) _=_; rw [credential,if_pos rfl,atO _ _ none,if_pos rfl]
    · intro j _ hj; change feeF b _=0; rw [credential,if_neg hj]
    simp
lemma Regal_lamp (ha:CrossP E): Regal c N (lampShelf E i)=lampShelf E i:=by
    unfold lampShelf; rw [map_sum]; exact sum_congr rfl fun j _=> Regal_loan _ _ _ (headQB j _ _ none (ha.num i _) (ha.gauge _) (ha.real _ _)) -- names inspect
lemma phase_lamp: Phases (lampShelf E i):=by intro w hw; unfold lampShelf; rw [map_sum]; exact sum_congr rfl fun j _=> phaseLoan j _ _ w hw
lemma mud_lamp: mud (lampShelf E i)=0:=by change clay c N _=_; unfold lampShelf; rw [map_sum]; exact sum_eq_zero fun _ _=> mudLoan ..
lemma gauge_lamp (k: Frame c) : sways (Lat.rotates N k) (lampShelf E i)=lampShelf E i:=by unfold lampShelf; rw [map_sum]; exact sum_congr rfl fun j _=>Subtype.ext ((shadeLoan j _ _) 1 k)
lemma turn_lamp (hp:Warrant v g k) (j:ι)(h:E.addr j=rotateL (E.addr i) v)(hc:Phases (E.view i 1))(hz:∀ V, Diode N v k g (E.view i (sky v V))=E.view j V)(hv:shadeG (E.view i))(he:Gated (E.addr i).support (E.view i 1)): Diode N v k g (lampShelf E i)=lampShelf E j:=by
    have he(x:Flavor N): lane E x j none=k*lane E x i none *star k:=by have hA := whirlB x _ _ (E.view j) none hp hc hz hv he; change mote _ _ _ none= (1:ℂ) • _ at hA; rw [one_smul,← h] at hA;exact hA
    unfold lampShelf; rw [map_sum]; refine sum_congr rfl (fun x _=>?_); rw [he,h]; exact turnLoan x _ _ hp
-- total estimate scalar and lamp. words at same anchor.
def widthB : ℝ:= Classical.choose preMoment
lemma widthB_le : 1 ≤ widthB:= (Classical.choose_spec preMoment).1
def jointFee (N:ℕ):ℝ:= N*(priceP N*widthB)
lemma joint_valid (N:ℕ):0 ≤ jointFee N:=by have hz:=priceP_nonneg (N:=N); unfold jointFee; positivity [widthB_le]
lemma shelfBudget (h:Woven (E.addr i).site (E.addr i).support p t (E.view i) r)(hp:0<t): Woven (E.addr i).site (E.addr i).support p t (fun _=>lampShelf E i) (jointFee N*r) := by
   let a0:= (E.addr i)
   let t₀ (b:Flavor N):=(lane E b i none); let Q b:=priceP N*(t^2*‖t₀ b‖); have hS := Woven.sumX (fun b:Flavor N=>fun _=> lightP1 b a0.site (t₀ b)) univ Q (p:=p) (fun b _=> costLoan b _ _ a0.support a0.anchor hp); rw [show (fun _:Grid c=>lampShelf E i)=(∑ b:Flavor N, (fun _=> lightP1 b a0.site (t₀ b))) from funext fun _=> by unfold lampShelf; rw [Finset.sum_apply]]; refine hS.stretches (Subset.refl _) ((sum_le_sum (g:=fun _=> priceP N*(widthB*r)) (fun b _=> ?_)).trans_eq ?_)
   · apply mul_le_mul_of_nonneg_left _ priceP_nonneg; unfold t₀ Stew.lane Stew.mote; split
     · exact ((Classical.choose_spec preMoment).2 c N b _ (E.view i 1) none t hp.le).trans (mul_le_mul_of_nonneg_left (h.sizeU 1 (AnalyticBridge.VerifiedReset.flat_ok ..)) (zero_le_one.trans widthB_le))
     rw [norm_zero,mul_zero]; exact mul_nonneg (zero_le_one.trans widthB_le) h.travel
   unfold jointFee; simp only [sum_const, Fintype.card_fin, card_univ, nsmul_eq_mul, Flavor]; ring
lemma sewBudget (h:Woven (E.addr i).site (E.addr i).support p t (E.view i) r)(hp:0<t): Woven (E.addr i).site (E.addr i).support p t (fun _=>sewShelf E i) r:=by
    apply constWoven _ _ _ (gator (E.addr i).support _); rw [vintage _ _ _ hp.le]; exact (sees _ _ hp.le).trans (h.sizeU 1 (AnalyticBridge.VerifiedReset.flat_ok ..))
end YM.QCD.Pith
#print axioms YM.QCD.Pith.shelfBudget
