import YM.Helio.Trust
import YM.Clays.Pinot
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
variable {T K:ℝ}
namespace Deposits
variable (h:Deposits U p σ T K)
include h
lemma thickP (hp:T≤ a)(ht:K≤ t): Deposits U p σ a t:=by obtain ⟨I,hX,Z,hT,rfl⟩:=h.art; exact ⟨I,hX,Z,hT.enlarge hp ht,rfl⟩
lemma duets (Y:St c)(hp:Deposits Y p σ w u):Deposits (U+Y) p σ (T+w) (K+u):=by
    obtain ⟨I,hX,Z,hT,rfl⟩:=h.art; obtain ⟨J,hY,M,h',rfl⟩:=hp.art; refine ⟨I⊕J,inferInstance,Sum.elim Z M,hT.duo M h',?_⟩; rw [Fintype.sum_sum_type]; rfl
lemma turnedY : Deposits (flipL ∘ U) p σ (‖clapL‖*T) (‖clapL‖*K):=by
    obtain ⟨I,hX,Z,hT,rfl⟩:=h.art; refine ⟨I,hX,fun i=>(Z i).turnover,hT.flopX,?_⟩; funext i; rw [comp_apply, Finset.sum_apply,map_sum,Finset.sum_apply]; simp_rw [ParcelZ.returnsT]; rfl
lemma volumeP (s:ℝ) : Deposits (s • U) p σ (‖s‖*T) (‖s‖*K):=by
    obtain ⟨I,hX,Z,hT,rfl⟩:=h.art; refine ⟨I,hX,fun i=>(Z i).rents s,hT.rentsX s,?_⟩; rw [smul_sum]; exact (sum_congr rfl fun i _=>ParcelZ.earnsT _ s).symm
end Deposits
abbrev linkR (V:Grid c)(x:Axis):Sheet c:= Stew.delta V x
def totalR (A:St c)(x:Axis):St c:=fun V=> linkR V x*A V-A V*linkR V x
lemma tplus (D E:St c) (x:Axis): totalR (D+E) x=totalR D x+totalR E x:=funext fun i=>by unfold totalR; simp only [Pi.add_apply,mul_add,add_mul]; abel
lemma twined (D:St c) (x:Axis)(hp:Deposits (fun V=> Lat.shift 0 V x * D V - D V*Lat.shift 0 V x) p σ T K) (he:foldH ∘ D=D): Deposits (totalR D x) p σ (‖(2:ℝ)⁻¹‖*(T+‖clapL‖*T)) (‖(2:ℝ)⁻¹‖*(K+‖clapL‖*K)):=by
    let s (V:Grid c):= Lat.shift 0 V x*(D V) - (D V)*Lat.shift 0 V x
    have hF: totalR D x=((2:ℝ)⁻¹) • (s+flipL∘s):=by
      funext V; obtain h := congr_fun he V; change foldH (D V)=_ at h; change ((2:ℂ)⁻¹ • _)*_- _* ((2:ℂ)⁻¹ • _)=(2:ℝ)⁻¹ • (s V+ foldH (s V)); rw [Matrix.smul_mul,Matrix.mul_smul,← smul_sub,show (2:ℂ)⁻¹=(((2:ℝ)⁻¹):ℂ) by simp, ← Complex.ofReal_inv,Complex.coe_smul]; apply congr_arg; unfold s; rw [sub_mul,mul_sub]; have hx:= tissue x V (D V); rw [h] at hx; rw [show _ - _ - (_ - _)= (Lat.shift 0 V x * D V-D V*Lat.shift 0 V x) - (star (Lat.shift 0 V x)*D V-D V*star (Lat.shift 0 V x)) by abel,hx,sub_neg_eq_add]
    rw [hF]; exact (hp.duets _ hp.turnedY).volumeP _
lemma procurement (B b n:ℕ){r:ℝ}(hK:CreditBeam r)(hσ:0≤σ):∃ S:ℝ,0 ≤ S∧∀ (c:Side)(x:Axis)(p:BudgetPoint)(A:St c)(η W:ℝ)(G:Silo c)(L:BankP c)(δ:ℝ), Run.Pack id id η δ B A W G L → Torch G→2*(σ+3)≤δ→ B ≤ p.B → p.power ≤ b→p.order ≤ n→p.threshold ≤η→ r*p.threshold<η/2→η≤1→ 0 ≤ W ∧ Deposits (totalR A x) p σ (S*W) (S*W*(p.threshold/η)):=by
    obtain ⟨T,hT,H⟩:=prepaid B b n hK hσ; refine ⟨‖(2:ℝ)⁻¹‖*(T+‖clapL‖*T),by positivity,fun c x p A η W G L δ hp hh hx hv hd he hr hb hz=>?_⟩
    obtain ⟨hC,hE⟩:= H c x p A η W G L δ hp hh hx hv hd he hr hb hz; exact ⟨hC,(twined A x hE (funext fun i=> soldF i G η δ W L A hp hh)).thickP (le_of_eq (by ring)) (le_of_eq (by ring))⟩ -- args
end Meridian
end YM.QCD.Entr
#print axioms YM.QCD.Entr.Meridian.procurement
