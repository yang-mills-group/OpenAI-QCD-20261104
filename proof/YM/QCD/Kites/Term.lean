import YM.QCD.Kites.Alone
/-! # Republication joint. state real param in theorem. uses separate issued Soft.
No smearing mask intertwines in K flights.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Kites
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N k B n b j:ℕ}{p:BudgetPoint}{η u a r t w P q J δ z z' θ σ d A ε T:ℝ}{i o:Site c}
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Pine YM.Next.Free Leaf LeafM Tee Garden Entr
variable {Γ:Silo c}{X:St c}{ι β ν α ι':Type}
local notation "V"=> EvenA c N
variable (G: Gem c N ι)(F: Rail c N β)(Y: Ruby.Hue c N ν)
variable (D:Site c)
def swarm (V': Grid c): V:=∑' i:ν,Y.mean i V'
-- early vacuum joint pressures; real chi hide constant. Reattach pre Core.tag etc. threshold uses emission flag.
noncomputable def heartS (t:ℝ)(u:Grid c→ℝ) (D':St c)(U:Grid c): V :=baker c N (u U)+nozzle c N (D' U)+ Patron.total G t U
noncomputable def heartK (T:ℝ)(U:Grid c): V:=∑' i,Ruby.tK F T U i
noncomputable def scoreV (T:ℝ)(v:Grid c→ℝ)(X:St c)(U: Grid c): V:= NormedSpace.exp (heartS G T v X U) * heartK F T U
noncomputable def scoreX (T:ℝ)(v:Grid c→ℝ)(X:St c)(U:Grid c): V:=scoreV G F T v X U* NormedSpace.exp (swarm Y U)
lemma routesC {G':Gem c N α} {v w:Grid c→ℝ}{D D': St c} (U:Grid c)(h : HasSum (fun i=>Y.mean i U) (heartS G T v D U - heartS G' T w D' U))
   (hp:Y.Tall T)(he:Summable (fun i=> ‖Ruby.sparkY Y U i‖))(ht:Summable (Ruby.tK F T U)): scoreV G F T v D U=scoreV G' (Ruby.Trail Y F T) T w D' U:=by
    let S':=swarm Y U; have hz : heartK (Ruby.Trail Y F T) T U=heartK F T U*exp S':= (Ruby.plenary Y F _ ht hp h.summable he).tsum_eq
    unfold scoreV; rw [hz,show (heartS G T v D U)=heartS G' T w D' U+ S' from ?_,exp_add]; · ring
    change _=_+ ∑' i,Y.mean i U; rw [h.tsum_eq]; abel
-- tune supplies difference absent old soft
lemma sunI {S:ℝ} (G:Gem c N α)(Y:Ruby.Hue c N ν)(H:Ruby.Hue c N ι)(hv: (Ruby.HJoin Y H).Tall S)(v u:Grid c→ℝ)(D D': St c)(E:Gem c N ι')(U:Grid c)(hp:Summable (Ruby.tK F S U))(hf: HasSum (fun i=> H.mean i U) (heartS G S v D U - heartS E S u D' U))(h:Summable (fun i=> ‖Ruby.sparkY (Ruby.HJoin Y H) U i‖))(hS:Summable fun i=>Y.mean i U):
    scoreX G F Y S v D U=scoreV E (Ruby.Trail (Ruby.HJoin Y H) F S) S u D' U :=by
    let W:=swarm Y U; let A:=Ruby.HJoin Y H
    have he:HasSum (fun i=>A.mean i U) (W+(heartS G S v D U - heartS E S u D' U)):= firmsM Y H _ _ U hS.hasSum hf
    have hs: swarm A U=W+(heartS G S v D U - heartS E S u D' U):= he.tsum_eq
    have hz : heartK (Ruby.Trail A F S) S U= heartK F S U *exp (W+(heartS G S v D U - heartS E S u D' U)):=by rw [← hs]; exact (Ruby.plenary A F U hp hv he.summable h).tsum_eq
    let G₁:= heartS G S v D U; let G₂:= heartS E S u D' U
    unfold scoreX scoreV; rw [show heartK _ S U=heartK F S U *_ from hz];
    change exp G₁*heartK F S U*exp W=exp G₂ * (_*exp (W+(G₁-G₂))); rw [mul_right_comm (exp G₁),←exp_add,mul_comm (heartK ..) _,← mul_assoc,←exp_add]; congr 2; abel
-- wave publication at actual threshold. ALSO carry unaltered calibrations.
lemma eff (x:Grid c)(u:ℝ)(T:ℝ)(v:Grid c→ℝ)(D:St c)(h: Summable (Ruby.tK F T x))(he:Summable (letters G p.threshold x))(hx:T=p.threshold): wearK c N u (scoreV G F T v D x)= scoreV (flightE G u) (flightK F u) T v (u^2 • D) x:=by
    unfold scoreV heartS; rw [map_mul,map_exp (wearK c N u) (songT (c:=c) (N:=N) u).continuous,map_add,map_add,juke,show wearK c N u (nozzle c N (D x))=paleF N (u^2 • D x) from tastes _ u _]; rw [show wearK _ _ u (heartK F T x)=heartK (flightK F u) T x from (story F x u T h).tsum_eq.symm,hx, ← (sour G x u he).tsum_eq]; rfl
end YM.QCD.Kites
