import YM.Oriole.Hoop
import YM.Tinus.ScalarB
/-! Fundamental phase read. financial Root error tied to Marquee, height panel.L. all X turn labels consistent. Any l. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Oriole
open QCD QCD.Lat QCD.Grass Lattice TensorProduct Function UV PCAC Filter MeasureTheory RG
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator ContDiff Classical TensorProduct
variable {d n:ℕ}(a b:Flavor 6)(g:Bool){c:Side}
open Poised.Display Poised.Stative Module Finset Revolve SourceRead Patria Patria.Depth TorusPCAC.Geometry Cylinder
local notation "Q"=> Massive.Run.plane
local notation "T"=> Lat.Fiber
local notation "ν" => Fintype.card Lat.Fiber
local notation "iso"=> MassFields.isotropic
local notation "F"=> flame a b g 8 (by decide)
local notation "L"=> arbor a b g
local notation "Gc"=> pulp g
variable {S:Scheme}{R:Side}{i j m:ℕ}(A:Run S n R 6)(p:Bool)(u:Averaging)(M:Spike)
local notation "Y"=> film Gc a b A p m
local notation "cP"=> S.side R i
local notation "J"=> Stiffness.body (A.density i) 1
local notation "f1"=> stalk M A a b p m
local notation "fS"=> stalk Gc A a b p m
local notation "yS"=> report A fS iso i 0
local notation "Δ"=> (Canvas.foil (A.density i) (yS)) 1
variable (h:A.Actual)(hj:i ≤ m)(hm:m ≤ n)(hP:a≠ b)
include h hj hm hP
-- body at LINK IDENTITY
lemma empty_path (w:Grid (S.side R i)): coef ∅ (report A f1 u i 0 w)= 0:=by
     let B:=report A f1 u i 0; let f:= ribbonK a; have he: Action.flavor f (⇑B)= -⇑B:= mindful a b a M hP A h u p hj hm (Or.inl rfl) 0; rw [dusk] at he; let F':= shaft a cP; have hz: coef ∅ (F' (B w))= coef ∅ (B w):=TorusPCAC.Ward.keeps_zero ..; have hp:F' (B w)= -(B w):= congr_fun he w; rw [hp,map_neg] at hz; exact neg_eq_self.mp hz
variable (H:TaperHol)(t x y:ℂ)(V:Label 8)
local notation "Ω"=> ((ratioTo S m i:ℝ)^4)
lemma E_bill (hT:Tally H 0 V (A.density i) (⇑yS)) (hQ:V=t • F+x • L true+y • L false)(D:ℝ) (hZ:‖diffS a b Gc H.T Δ‖ ≤ D) :
       ν * ‖ ((Ω:ℝ):ℂ)*t + PCAC.chord Gc a b A i (S.toStop R A.β A.w m i Y)‖ ≤ Ω * D :=by
     let B:= yS; let U:=Canvas.foil (A.density i) B 1; let V':= S.toStop R A.β A.w m i Y
     let W:= ((Ω:ℝ):ℂ)*t + PCAC.chord Gc a b A i V'; have hu : IsUnit ((A.density i) 1):= hT.unit.self_of_nhds
     have hz : (Fintype.card (Site (S.side R i)):ℂ) * ν * PCAC.chord Gc a b A i B = - spread a b PP Gc U:= primal a b (A.density i) _ (h.even (hj.trans hm) _) hu (empty_path a b A p iso Gc h hj hm hP _) Gc -- Nat*Nat? ✓
     have hy: (ν:ℂ)*W = -((Ω:ℝ):ℂ)*diffS a b Gc H.T Δ:=by
          have he :=orbitZ a b g (A.density i) B V H t x y hQ hT; unfold W; rw [show PCAC.chord Gc a b A i V'=((Ω:ℝ):ℂ)*Fintype.card (Site (S.side R i))*PCAC.chord Gc a b A i B from momentumR (S:=S) A Gc a b p (fun _=>2) Gc hj h hm]; rw [diffS, LinearMap.sub_apply]; change _= -((Ω:ℝ):ℂ)*(spread a b PP Gc U-spread a b (TP H.T) Gc U); rw [he,show (spread a b PP Gc U)=_ from neg_eq_iff_eq_neg.mp hz.symm]; -- actually need `hz`
          ring
     calc _= ‖(ν:ℂ)*W‖:= (by rw [norm_mul,Complex.norm_natCast])
          _= Ω * ‖diffS a b Gc H.T U‖:=by rw [hy,norm_mul,norm_neg,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
          _ ≤ _:= mul_le_mul_of_nonneg_left hZ (by positivity)
end YM.Massive.Oriole
#print axioms YM.Massive.Oriole.E_bill
