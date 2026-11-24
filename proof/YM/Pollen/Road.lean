import YM.Pollen.Loom
import YM.Pollen.Signal
import YM.Pollen.Aven
import YM.Pollen.Bolt
import YM.Pollen.Chonk
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Entr
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N k B n b j:ℕ}{p:BudgetPoint}{η u a r t w P q J δ z z' θ σ:ℝ}{i o:Site c}
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Pine YM.Next.Free Leaf LeafM Tee Garden
variable {Γ:Silo c}{A: BankP c}{U:St c}
namespace Meridian
open scoped Kronecker
open Grass.Ward Massive.PCAC
set_option quotPrecheck false
variable (F:Flavor 6)(Z:ParcelZ (c:=c))
variable (o: Site c) (J':Bool) (x:Axis)(Y:St c)
local notation "d"=> totalR Y x
local notation "R"=>zone 6 o
local notation "Ψ"=>Modes c 6
local notation "M"=>Sour Ψ
-- compare actual operation. introduces f row report exact on all fields. Later translation & sym
noncomputable def beacon (V:Grid c) : Fields c 6→L[ℂ] Fields c 6:= mixΛ (keel o x F) (keelB o x F) V
local notation "hx" p:arg=> beacon F p x -- param order.N Lean.L
noncomputable def sourceT (V:Grid c): EvenA c 6 := cream (copies 6 (Y V)*keel o x F V-keelB o x F V*copies 6 (Y V))
local notation "Y∗"=>sourceT F o x Y
local notation "Z!"=> aurasigmaMont F o x Y
lemma authenticR (V:Grid c) : light _ (Y∗ V)= ((hx o) V) (light _ (nozzle c 6 (Y V))):=by
    change form _= applyMark false _ (form _)-applyMark true _ (form _); rw [mark_forms,mark_forms]; exact form_sub ..
lemma hands (V:Grid c): ∑ o:Site c,sourceT F o x Y V= ∑ o:Site c, aurasigmaMont F o x Y V:=by
    unfold sourceT; rw [← map_sum,honing]; let X:=Y V; let D:= delta V x; let S:= copies 6 X; let T':=capsΛ F D; have hv:∑ p:Site c,keel p x F V=T':=by unfold keel; rw [←sum_mul,cells,one_mul]; rfl
    have hu:∑ p:Site c,keelB p x F V=T':=by unfold keelB; rw [←mul_sum,cells,mul_one]; rfl
    rw [sum_sub_distrib,← mul_sum,← sum_mul,hv,hu,show -bouquet F (totalR Y x V)=cream (-(capsΛ F (totalR Y x V))) from (map_neg cream ..).symm]; apply congr_arg; change S*T'-T'*S= -capsΛ F (D*X-X*D); rw [map_sub,neg_sub]; apply congr_arg₂ (·-·) -- see spot factor
    · rw [show S=X ⊗ₖ 1 from Sway.choir_in ..]; unfold T'; change (X ⊗ₖ 1)*(D ⊗ₖ Massive.PCAC.spot F F)= _; rw [← Matrix.mul_kronecker_mul,one_mul]; rfl
    rw [show S=X ⊗ₖ 1 from Sway.choir_in ..]; unfold T'; change (D ⊗ₖ Massive.PCAC.spot F F)*(X ⊗ₖ 1) = _; rw [← Matrix.mul_kronecker_mul,mul_one]; rfl
noncomputable def forkT := Z!-Y∗
local notation "Uμ"=>forkT F o x Y
noncomputable def forgeT (X:Massive.Density c 6) (V:Grid c):= (beacon F o x V) (X V)+X V*(Uμ V).val
lemma totalV (K:Massive.Density c 6) : (∑ o:Site c, forgeT F o x Y K)=(∑ o:Site c,(fun V=>(beacon F o x V) (K V))):=by
    funext p; simp only [Finset.sum_apply,forgeT,forkT,Pi.sub_apply,sum_add_distrib]; rw [← mul_sum, show (∑ i:Site c,Subtype.val (aurasigmaMont F i x Y p-sourceT F i x Y p))=0 from ?_,mul_zero,add_zero]
    change (∑ i: Site c, (light _) (aurasigmaMont F i x Y p-sourceT F i x Y p))=0; rw [← map_sum, sum_sub_distrib,hands F x Y,sub_self,map_zero]
-- generic request.Rep.X for tilde budget
open MassiveQCD MassiveQCD.Sample.Basal MassiveQCD.Sample.Basal.WindowU
local notation "w!"=> Fintype.card -- collides v
variable {I:Type}[Fintype I](oK:I→Site c)(σ':I→ℂ)
local notation "η0"=> (fingers 6)^2*a^2
local notation "t*"=> (fun j=>σ' j • (forkT F (oK j) x Y))
variable (hx0:∀ j, Suit (oK j) p η (beacon F (oK j) x))
include hx0
open Plate Ribbon Cupola Cape
lemma maturity (A:Set (Finset I))(hk:∀ i∈ A,i.card ≤1)(hp:0<a)(ht:0 ≤ u)(hz:∀ j,‖σ' j‖≤u)(hD: Deposits (totalR Y x) p σ t w)(s:List I)(he:s.Nodup)(hR:∀ i,i∈s):∃ (D1 D2:Type)(_ : Countable D1)(_ : Countable D2)(R':Reel c 6 I D1)(Q:Lure c 6 I D2),CarryT oK R' Q p a σ ((w! I:ℕ)* (u*(η0*w))) ((w! I:ℕ)*(u*(η0*t))) A ((deltaU oK (fun j V=> beacon F (oK j) x V) hx0 σ' s (fun V=> rootR (Spine I) (Keys c 6) (nozzle c 6 (Y V))))+vaultU t*):=by
    have hP(j:I): MassiveQCD.Sample.Basal.WindowU.Given (oK j) p a σ (u*(η0*w)) (u*(η0*t)) (σ' j • (aurasigmaMont F (oK j) x Y)):=by
           obtain ⟨D,hD',Z,H,hY⟩:=hD.art; obtain ⟨f',g',b',hf,hg,hk⟩:=H.book; have ht:= budget_nonneg (hg (oK j)); have hd:= budget_nonneg (hk (oK j)); have h0:0≤ η0:=mul_nonneg (sq_nonneg _) (sq_nonneg _); exact Given.adoptsA _ _ (Given.units _ _ (eraX F (oK j) x Y hp hD) (σ' j)) (mul_le_mul_of_nonneg_right (hz j) (mul_nonneg h0 hd)) (mul_le_mul_of_nonneg_right (hz j) (mul_nonneg h0 ht))
    obtain ⟨D1,D2,hD1,hD2,R',Q,hZ⟩:= Given.stakes oK A _ hP hp
    refine ⟨_,_,hD1,hD2,R',Q,astral oK _ hx0 σ' s A R' Q hZ he hR hk ?_⟩
    intro j V; let y:=sourceT F (oK j) x Y V; let z':= aurasigmaMont F (oK j) x Y V
    change light _ ((σ' j) • z')= _ + light _ ((σ' j) • (z'-y)); rw [map_smul,map_smul,map_sub,← show light _ y =_ from authenticR F (oK j) x Y V,smul_sub]; abel
end Meridian
end YM.QCD.Entr
#print axioms YM.QCD.Entr.Meridian.maturity
#print axioms YM.QCD.Entr.Meridian.totalV
