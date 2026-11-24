import YM.VMarker.Clause
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Plate
open QCD Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph QCD.GasP PhysicalNext.Repeat.Turn Patron Kites Ribbon Cupola Relight Ruby
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N:ℕ} {I J U V E: Type}[Fintype I]
variable {t v u a w B:ℝ}{k:ℕ} (p:I→ Site c)(θ:ℝ) (S:Support c)
local notation "M"=> Ribbon.ample N I
local notation "K"=> Keys c N
local notation "R"=> Spine I
local notation "b!"=> banknote N p θ
structure LidW (p:Patron.Rail c N J)(t b:ℝ)(k:ℕ)(A U:ℝ) : Prop where
   uses : p.Reg t
   sold : Quits p k 1 U A b
variable (N)(q:I→Bool)(F: Patron.Rail c (ample N I) U)(φ r:ℝ)
local notation "pay₀"=> changeBill N p r φ θ
local notation "P"=> pursue N p θ F φ r
variable (w:ℝ)
lemma portageL (h:LidW F t φ k a w)(hv:0 < r)(hr:0 < θ)(hp:r*θ ≤ φ)(he:∀ i U,Well N p φ q (F.warp i U)) : LidW P t θ k a w :=by
     have h0:= (mul_pos hv hr).trans_le hp; have hs:= h.uses; constructor
     · exact ⟨fun i U V hu hx=>congr_arg pay₀ (hs.uses i U V hu hx), fun i=> (pay₀).toLinearMap.toContinuousLinearMap.continuous.measurable.comp (hs.reads i), fun i U=> change_L N p r φ θ _ _ (hs.role i U),fun i U hh=>hs.buys i U (fun hp=> hh ((congr_arg pay₀ hp).trans (map_zero _)))⟩
     obtain ⟨u,hu,H⟩:=h.sold.cost; exact ⟨u,hu,fun i U=> (changeCoin N p r φ θ q _ (he i U) hv hr hp).trans (H i U)⟩
end YM.MassiveQCD.Plate
namespace YM.MassiveQCD.Plate
open QCD Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph QCD.GasP PhysicalNext.Repeat.Turn Patron Kites Ribbon Cupola Relight Ruby
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c f L:Side}{m k l N:ℕ} {I J U E:Type}[Fintype I]
variable {a A C v w t:ℝ}{O: BudgetPoint}
variable (N)(p:I→Site c)(q:I→Bool)(θ φ r:ℝ)(Y: Ruby.Hue c N J)(F: Patron.Rail c (ample N I) U)
local notation "M"=> Ribbon.ample N I
local notation "K"=> Keys c N
local notation "R"=> Spine I
local notation "b!"=> banknote N p θ
local notation "b'"=>banknote N p φ
local notation "d!"=> withdraw N p θ
local notation "F!"=> pursue N p θ F φ r
local notation "Y!"=> radial I Y
local notation "K!"=> limb N p θ φ r Y F
open ConnectedActivityE6 Pressure Pressure.Stores OrbitG Sway
variable (h:LidW F t φ O.B v w)(hY:Wax Y t O.B A a θ)(ht:∀ i, shadeG (Y.mean i)) (hp:0< r)(hv:1 ≤θ)(hw:r*θ ≤ φ)(he:0 ≤ A)(hθ:1 ≤w)(hr:0≤v) (hk:∀ i U, Well N p φ q (F.warp i U))
include hk hv h hY he hθ hr hv hw hk hp
lemma palmedL (hm :1≤φ) (V:Grid c) : let _P:= F!; let x:= K! t; Kites.heartK x t V= changeBill N p r φ θ (Kites.heartK F t V)* NormedSpace.exp (Apron.bearing I c N (Kites.swarm Y V)):=by
   intro P R'; have hh:=zero_lt_one.trans_le hv; have hi:= portageL N p θ q F φ r w h hp hh hw hk; have ht := WaxGov (I:=I) θ Y hY
   -- hφ may <1 if r small & target; raw F may not spend at ⦃≥1⦄ then `thermal.z` supplies at true φ≥1. add assumption.
   let Z:= changeBill N p r φ θ; have hB:heartK P t V= Z (heartK F t V):=by
       unfold Kites.heartK; let p':= Z.toLinearMap.toContinuousLinearMap; change _=p' _; rw [p'.map_tsum (profits _ V hm hθ h.sold hr t)] -- rw p defeq?
       refine tsum_congr (fun i=>?_); change tK P t V i=Z _; unfold tK; split; rename_i hf; rw [if_pos (show (separated (blocked (Ruby.home F)) i ∧ RG.flags t V = i.biUnion (oriD F)) from hf)]; exact (map_prod Z ..).symm; rename_i hf; rw [if_neg (show ¬(separated (blocked (Ruby.home F)) i ∧ RG.flags t V = i.biUnion (oriD F)) from hf)]; exact (map_zero Z).symm -- if need proof eq
   obtain ⟨h₁,h₂⟩:= ht.heated hv he V; refine (plenary (Y!) P V (profits P V hv hθ hi.sold hr t) ht.burns h₁ h₂).tsum_eq.trans ?_; rw [show (∑' i,tK P t V i)=Z (heartK F t V) from hB]; apply congr_arg; apply congr_arg; exact ((Apron.bearing I c N).toLinearMap.toContinuousLinearMap.map_tsum (hY.heated hv he V).1).symm
-- bounds include Loom.Power threshold.END
end YM.MassiveQCD.Plate
namespace YM.MassiveQCD.Plate
open QCD Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph QCD.GasP PhysicalNext.Repeat.Turn Patron Kites Ribbon Cupola Relight Stew Ruby Coda Reggae
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{m k B N:ℕ}{s t h a r η σ Γ α δ:ℝ}{P:BudgetPoint}{J D I V E W K₀:Type}[Fintype I]
local notation "Z"=> Keys c N
local notation "R"=> Spine I
local notation "M"=> Ribbon.ample N I
local notation "Π'"=>Patio (Keys c N⊕Spine I)
variable (N)(p:I→Site c)(q:I→Bool)(φ θ r₀:ℝ)
local notation "w"=> withdraw N p φ
local notation "u"=> withdraw N p θ
local notation "O'"=> rootR R Z
local notation "Ω0"=>vacR R Z
variable (G: Gem c (ample N I) E)(Ω:E→Finset I)(A:Set (Finset I))(Y: Ruby.Hue c N V)(F: Patron.Rail c (ample N I) W)(K: Patron.Rail c N K₀)
local notation "f!"=> faultK N p φ F
local notation "K'"=> limb N p θ φ r₀ Y F -- combined post. 
local notation "F'"=> Reel.render N p φ r₀ G Ω A
set_option quotPrecheck false
local notation "Q⁔"=> Trail Y (flightK f! r₀) P.threshold
local notation "Faber"=> K' P.threshold
local notation "Σ'"=> Film.publication N p q Faber A θ
local notation "p₀"=> (turn I (D:=Z) r₀).comp w
variable (A₀ R': Grid c→ EvenA c N) (Tt : Finset I)(χ:Grid c)
-- A₀= baker + paleF in unmarked DOF. R'= entire successor exponent after (incl factored analytic scalar correction).
local notation "★"=> Film.publication N p q Faber A θ
local notation "op"=> shutter Z Tt
variable (hF:LidW F P.threshold φ P.B a t)(hY: Wax Y P.threshold P.B α δ θ)(hE:∀ i,shadeG (Y.mean i))(hz:Correspond (Trail Y (flightK (faultK N p φ F) r₀) P.threshold) K)(hr:0 < r₀)(hθ:1 ≤ θ)(hr':1 ≤ φ)(hp:r₀ * θ ≤ φ)(ht:1 ≤ t)(ha:0 ≤ a)(hα:0 ≤ α)
variable (hK:∀ i V,Well N p φ q (F.warp i V))
variable (hW: ∀ i V,Mint N p φ q (Ω i) (G.view i V)) (hL:Summable (letters G P.threshold χ))(hU:G.Gather)(hf0:(Tt.powerset:Set (Finset I))⊆ A)
variable (h1:Pill (limb N p θ φ r₀ Y F P.threshold) P.threshold θ P.B η s)(hh:1 ≤ s)(hh':0≤ η)
-- maybe not need s comparison if use fiscal by directing h.K. from grant confidence. Still OK
variable (M':ℝ)
include hF ht hθ hY hα ha hp hr hr' hK
lemma warmedL :
   u (heartK (Faber) P.threshold χ)= p₀ (heartK F P.threshold χ)* NormedSpace.exp (O' (Kites.swarm Y χ)):=by
      rw [palmedL N p q θ φ r₀ Y F hF hY hr hθ hp hα ht ha hK hr' χ] -- arg order
      rw [map_mul,map_exp u (u).toLinearMap.continuous_of_finiteDimensional]; apply congr_arg₂ (·*·)
      · exact changeLife N p θ φ r₀ _ (zero_lt_one.trans_le hθ)
      apply congr_arg; rw [← real_sector p θ,Cupola.home N _ _ (zero_lt_one.trans_le hθ)] -- sig real
end YM.MassiveQCD.Plate
namespace YM.MassiveQCD.Plate
open QCD Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph QCD.GasP PhysicalNext.Repeat.Turn Patron Kites Ribbon Cupola Relight Ruby
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c f L:Side}{m k l N:ℕ} {I J U E:Type}[Fintype I]
variable {a A C v w t:ℝ}{O: BudgetPoint}
variable (N)(p:I→Site c)(q:I→Bool)(θ φ r:ℝ)(Y: Ruby.Hue c N J)(F: Patron.Rail c (ample N I) U)
local notation "M"=> Ribbon.ample N I
local notation "K"=> Keys c N
local notation "R"=> Spine I
local notation "b!"=> banknote N p θ
local notation "b'"=>banknote N p φ
local notation "d!"=> withdraw N p θ
local notation "F!"=> pursue N p θ F φ r
local notation "Y!"=> radial I Y
local notation "K!"=> limb N p θ φ r Y F
namespace Wage
set_option quotPrecheck false
open QCD.Villa QCD.Leaf QCD.Loom QCD.Loom.Fleet QCD.Stew QCD.High QCD.Acre QCD.Meridians QCD.Kites
local notation "bz"=> O.threshold
open QCD.Leaf QCD.Jets
open QCD.Kites Coda QCD.Finch
variable {C' W V:Type}{x z ν β ε:ℝ}
open Sway
-- through fields at chosen horizon threshold with witnesses
structure Lump (X:Patron.Rail c (ample N I) U)(P:BudgetPoint)(t η w:ℝ):Prop where
   tilt:LidW X P.threshold t P.B η w
   fits:∀ i V,Well N p t q (X.warp i V)
lemma travelsX (H:Lump N p q F O φ v w)(hY: Wax Y O.threshold O.B a A θ)(hP:∀ i,shadeG (Y.mean i))(h:0<r)(hr:r*θ ≤ φ)(hs:StackK O.B w z v β a A)(hz:1 ≤θ) : Lump N p q (limb N p θ φ r Y F O.threshold) O θ β z:=by
    let Z:= pursue N p θ F φ r; let W:= radial I Y; have hv :0<θ:=zero_lt_one.trans_le hz
    exact ⟨⟨plant _ _ (WaxGov (I:=I) θ Y hY).burns (portageL N p θ q F φ r w H.tilt h hv hr H.fits).uses,hs c M J U W Z O.threshold θ (WaxGov (I:=I) θ Y hY|>.expense) (portageL N p θ q F φ r w H.tilt h hv hr H.fits|>.sold)⟩,fun i V=> engraved N p q θ φ r Y F hz H.fits V i⟩
variable (X:Ruby.Hue c N C')(Z:Ruby.Hue c N W) (G: Patron.Rail c N V)
variable (O)
-- prepare using Switch. track precisely θ/phase
open QCD.Jets.Touch
local notation "St"=>speedP L t x
local notation "Ft"=>fan L t x
local notation "gn"=> Kites.run L x -- verify
variable (hX: Switch (N:=N) O L x t φ ε A)
local notation "Lg"=> limb N p (speedP L t x) φ 1 Y F O.threshold
local notation "Xg"=> limb N p (fan L t x) (speedP L t x) r X (Lg) O.threshold
local notation "Zg"=> limb N p (fan L t x) (fan L t x) 1 Z (Xg) O.threshold
open ConnectedActivityE6 QCD.Kites
local notation "pr"=> pra L (run L x)
variable (hY: Purchases Y O.threshold O.B (1+1+1) (pra L (run L x)) (speedP L t x))(h₁:Purchases X O.threshold O.B (1/8+1/8+1) 1 (fan L t x))(h₂:Wax Z O.threshold O.B (7*(1/32)+1) 1 (fan L t x)) (h₃:∀ i,shadeG (Z.mean i))
variable (hβ:Lump N p q F O φ (1+1) (priceK L ε (run L x)))(hk:1 ≤ priceK L ε (run L x))(hr:0 < r)(hv:r ≤ 2)
open Sway
local notation "f!"=>faultK N p φ F
local notation "Z!"=> Trail Z (Trail X (flightK (Trail Y (faultK N p φ F) O.threshold) r) O.threshold) O.threshold
local notation "β!"=> (turn I (D:=K) r).comp (withdraw N p φ)
local notation "Ro" => rootR R K
variable (hZ:Correspond (Ruby.Trail Z (Ruby.Trail X (flightK (Ruby.Trail Y (faultK N p φ F) O.threshold) r) O.threshold) O.threshold) G)
include hX
include hY h₁ h₂ hβ hk hr hv h₃
lemma growthL [Countable J] [Countable U] : Lump N p q (Zg) O Ft (3/16) (taxK L x 4)∧∀ V:Grid c, withdraw N p Ft (heartK Zg O.threshold V)= (β!) (heartK F O.threshold V) *Ro ((wearK c N r (exp (swarm Y V))*exp (swarm X V))*exp (swarm Z V)):=by
    have hz:= hX.count; have hF:0 < Ft:=zero_lt_one.trans_le hz; have hS:1 ≤ St:=by unfold speedP; linarith; -- trailing
    have hφ: 1*St≤ φ:= (one_mul _).le.trans hX.steer; have hr':r*Ft ≤ St:= mul_le_mul_of_nonneg_right hv hF.le
    have he: Wax Y O.threshold O.B (1+1+1) pr St:=⟨hY.life,cashSoft _ hY⟩; have he': Wax X O.threshold O.B (1/8+1/8+1) 1 Ft:=⟨h₁.life,cashSoft _ h₁⟩
    have hu:= travelsX N p q St φ 1 Y F hβ he hY.projection.gauge zero_lt_one hφ hX.path hS
    have hQ :Countable (Plot (radial I Y) (pursue N p St F φ 1)):= QCD.Acre.Rails.glazeP .. -- fix
    have hL: Lump N p q Lg O St (1/8+1/8) (taxK L x 8):=⟨⟨hu.tilt.uses,Kites.tide (p:=O) Lg (liveK Lg hu.tilt.sold (by norm_num) (zero_lt_one.trans_le hS) le_rfl) (Real.exp_pos _).le hX.blaze⟩,hu.fits⟩
    have ht':= travelsX N p q Ft St r X Lg hL he' h₁.projection.gauge hr hr' hX.pool hz
    have hp' : 1*Ft≤ Ft:=by rw [one_mul]
    have hw(k:ℝ)(h:0 ≤ k):1 ≤ taxK L x k:=Real.one_le_exp (mul_nonneg h (fan_pos ..).le)
    refine ⟨travelsX N p q Ft Ft 1 Z Xg ht' h₂ h₃ zero_lt_one hp' hX.quilt hz, fun U'=>?_⟩
    have ha := warmedL N p q Ft Ft 1 Z Xg U' ht'.tilt h₂ zero_lt_one hz hz hp' (hw 6 (by norm_num)) (by norm_num) (by norm_num) ht'.fits
    have hb := warmedL N p q St Ft r X Lg U' hL.tilt he' hr hz hS hr' (hw 8 (by norm_num)) (by norm_num) (by norm_num) hL.fits
    have hc := warmedL N p q φ St 1 Y F U' hβ.tilt he zero_lt_one hS (hS.trans hX.steer) hφ hk (by norm_num) (by norm_num) hβ.fits
    simp_rw [AlgHom.comp_apply,turn₁] at ha hc; rw [AlgHom.comp_apply] at hb
    rw [ha,hb,hc,map_mul (Plate.turn I r),map_exp (Plate.turn I r) ((Plate.turn I (D:=K) r).toLinearMap.toContinuousLinearMap.continuous),rollRoot]
    simp only [map_mul Ro,map_exp Ro (Ro).toLinearMap.toContinuousLinearMap.continuous, map_exp (wearK c N r) (Loom.Fleet.songT (c:=c) (N:=N) r).continuous,AlgHom.comp_apply]; ring
end Wage
end YM.MassiveQCD.Plate
namespace YM.MassiveQCD.Plate
open QCD Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph QCD.GasP PhysicalNext.Repeat.Turn Patron Kites Ribbon Cupola Relight Ruby
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c f L:Side}{m k l N:ℕ} {I J U E:Type}[Fintype I]
variable {a A C v w t:ℝ}{O: BudgetPoint}
variable (N)(p:I→Site c)(q:I→Bool)(θ φ r:ℝ)(Y: Ruby.Hue c N J)(F: Patron.Rail c (ample N I) U)
local notation "M"=> Ribbon.ample N I
local notation "K"=> Keys c N
local notation "R"=> Spine I
local notation "b!"=> banknote N p θ
local notation "b'"=>banknote N p φ
local notation "d!"=> withdraw N p θ
local notation "F!"=> pursue N p θ F φ r
local notation "Y!"=> radial I Y
local notation "K!"=> limb N p θ φ r Y F
namespace Wage
set_option quotPrecheck false
open QCD.Villa QCD.Leaf QCD.Loom QCD.Loom.Fleet QCD.Stew QCD.High QCD.Acre QCD.Meridians QCD.Kites
local notation "bz"=> O.threshold
open QCD.Leaf QCD.Jets
variable {V J₁ K₀:Type} (G:Patron.Gem c (ample N I) E)(Ω:E→Finset I)(A':Set (Finset I))(Q: Patron.Rail c (ample N I) J₁)(K₁ : Patron.Rail c N K₀)
local notation "F'"=> Reel.render N p φ r G Ω A'
local notation "Σ'"=> Film.publication N p q Q A' θ
local notation "Λ'"=> turn I (D:=K) r
open QCD.Jets.Touch
variable (A₀ R': Grid c→ EvenA c N) (Tt : Finset I)(χ:Grid c)
local notation "w'"=> withdraw N p φ
local notation "u'"=> withdraw N p θ
local notation "O'"=> rootR R K
local notation "Ω0"=>vacR R K
local notation "op" => shutter K Tt
variable (hE:∀ i V,Mint N p φ q (Ω i) (G.view i V))(hG:G.Gather)(hH: Summable (letters G O.threshold χ))(hV:(Tt.powerset:Set (Finset I))⊆ A')(hp:Lump N p q Q O θ v w)(hC: Correspond (faultK N p θ Q) K₁)(hv:1 ≤ w)(hz:0 ≤ v)(hθ: 1 ≤ θ)(hφ:0<φ)
include hE hG hH hV hp hC hv hz hθ hφ
lemma clauseL (C:ℂ)(M':EvenA c N)(hx: u' (heartK Q O.threshold χ) = Λ' (w' (heartK F O.threshold χ))*O' M')(hm:wearK c N r (NormedSpace.exp (A₀ χ+ Ω0 (w' (Patron.total G O.threshold χ)))) = C • (exp (R' χ)*M')) : op (turn I r (outset N p φ G F A₀ χ (P:=O)))= C • op (relativeE N F' Σ' K₁ R' O.threshold χ):=by
     let V:= Patron.total G O.threshold χ; let H:= Reel.rope F' O.threshold χ
     have he:= Reel.presenceD N p q φ r G Ω A' hE hφ hG χ Tt hH hV
     let So:= A₀ χ+ Ω0 (w' V); let q':=wearK c N r
     have hEq : op (Λ' (O' (A₀ χ)+w' V))=op (O' (q' So)+H):=by
          unfold q' So; rw [map_add (wearK c N r), ← freeTurn,map_add (O'),map_add (Λ'),rollRoot,add_assoc,map_add op,map_add op,map_add op]; rw [map_add op] at he; exact congr_arg _ he
     have hθ':=zero_lt_one.trans_le hθ; let S':= Σ'; have hk:= Film.mergeFront N p q θ K₁ Q A' Tt hV hp.fits hθ' hp.tilt.uses hC χ (prints _ _ hp.tilt.uses hp.tilt.sold hv hz hθ)
     let T:= Reel.rope F' O.threshold χ; let Qx:= heartK F O.threshold χ
     unfold relativeE outset; rw [map_mul op,map_mul (Λ'),map_mul op,map_exp (Λ') (Λ').toLinearMap.toContinuousLinearMap.continuous,map_exp op (op).toLinearMap.toContinuousLinearMap.continuous,hEq,hk,Film.testifyK,hx]; -- check order map_mul rhs
     rw [← map_exp (op) (op).toLinearMap.toContinuousLinearMap.continuous]; -- turn pulls
     rw [exp_add, ←map_exp (O') (O').toLinearMap.toContinuousLinearMap.continuous, ←map_exp q' q'.toLinearMap.toContinuousLinearMap.continuous,show q' (exp So)=_ from hm]; simp only [map_smul,map_mul O',map_mul op,exp_add,←map_exp O' (O').toLinearMap.continuous_of_finiteDimensional,← map_exp O' (O').toLinearMap.toContinuousLinearMap.continuous,Algebra.smul_mul_assoc]
     change C • _= C • (op (O' (exp (R' χ)))*op (exp H)*(op (Λ' (w' Qx))*op (O' M'))); apply congr_arg; ring
end Wage
end YM.MassiveQCD.Plate

#print axioms YM.MassiveQCD.Plate.Wage.growthL
#print axioms YM.MassiveQCD.Plate.Wage.clauseL
