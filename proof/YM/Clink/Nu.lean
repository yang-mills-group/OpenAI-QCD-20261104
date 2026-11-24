import YM.Clink.Birds
/-! Tilt at frost paid via adjustment split. Genuine agency at alignment x.Sa. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.QCD.Entr.Meridian
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator Kronecker
variable {c:Side}{N k B n b j:ℕ}{p:BudgetPoint}{η u a r t w P q J δ z z' θ σ C C' α α' ξ M:ℝ}{i o: Site c}
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Pine YM.Next.Free Leaf LeafM Tee Garden
open WardBin.Lies Eyrie Rudder Massive.PCAC
open MassiveQCD MassiveQCD.Sample.Basal.WindowU
open Pressure WilsonStartup
open QCD.Kites QCD.Fork QCD.Fount QCD.Jets QCD.Raft QCD.Raft.ParcelR QCD.Jets.Touch
variable {Ψ:ParcelR}(H:SunR Ψ)(L:Side)(P':Plan j)
local notation "Ξ" b:arg=> haloK L b
structure AffairR (P':Plan j)(L:Side)(Ψ:ParcelR)(n b:ℕ)(σ C x:ℝ):Prop where
     ready :∀ (c:Side)(V:Train j)(U:SunR Ψ)(dY:Axis)(o:Site c)(p: BudgetPoint),p.threshold=fiery su x L → p.B=highR L x → p.power ≤ b → p.order ≤ n→ ∀ (a:Flavor 6)(t:ℝ),0<t→ ∀ m:ℝ, let A : St c:= wood P' 0 V + (fun _=> m • (1:Sheet c)); Given o p t σ (C*t^2*p.threshold) (C*t^2) (aurasigmaMont a o dY A+sourceT a o dY (blossomT U.X U.Y (haloK L x) c))
lemma hires (hp:Ψ.Rates a)(n b:ℕ)(hσ:0≤σ):∃ C:ℝ,0 ≤ C ∧∀ᶠ x in atTop,AffairR P' L Ψ n b σ C x:=by
       obtain ⟨r,h⟩:=solvent
       obtain ⟨B,T,δ,hT,hD,hV,H⟩:= forestry P' b n hσ h; obtain ⟨C0,B0,ε,hC,hε,hQ0⟩:= crisp (show 0<1 by norm_num) hp.hr Ψ.c hσ n b; obtain ⟨C1,B1,ε',h1,hε',hQ1⟩:= crisp (show 0<2 by norm_num) hp.hs Ψ.d hσ n b
       let C:=fingers 6^2*(T/δ)+C0+C1; refine ⟨C,by unfold C; positivity,?_⟩
       filter_upwards [buysL L h hD B,buysL L h hε B0,buysL L h hε' B1] with x hx hB hM
       refine ⟨fun c V U dY o p hθ hβ ht hK a t h0 m=>?_⟩; intro A; let M:= p.threshold; let Z:= haloK L x; have hx':0< Z:= hx.1; have hh:Z ≤1:=hx.2.1; obtain ⟨hB',h',hz⟩:=hx.2.2 p hθ hβ; have he: totalR A dY=totalR (wood P' 0 V) dY:=by
               let f(_:Grid c):= m • (1:Sheet c); unfold A; rw [tplus, add_eq_left]; funext V; change _ * f V-f V*_=0; unfold f; rw [Matrix.mul_smul,Matrix.smul_mul,mul_one,one_mul,sub_self]
       have hA:Deposits (totalR A dY) p σ T (T/δ*M):= he ▸ H c V dY p ht hK hB' (h'.trans (mul_le_of_le_one_right hD.le hh)) (hz.trans_le (div_le_div_of_nonneg_right (mul_le_of_le_one_right hD.le hh) (by norm_num)))
       let c1:= sourceT a o dY (wild (frosting U.X.W) Z c); let c2:= sourceT a o dY (wild (frosting U.Y.W) Z c)
       rw [show sourceT a o dY (blossomT U.X U.Y (haloK L x) c)= c1+c2 from joined' ..]; obtain ⟨hB,hP,-⟩:= hB.2.2 p hθ hβ; obtain ⟨hY,hP',-⟩:=hM.2.2 p hθ hβ
       refine Given.adoptsA _ o (Given.plies _ o (eraX a o dY A h0 hA) (c1+c2) (Given.plies _ o (hQ0 _ _ p ht hK hB _ hx' hh hP t h0 a o dY) c2 (hQ1 _ _ p ht hK hY _ hx' hh hP' t h0 a o dY))) (le_of_eq (by unfold C M; ring)) ?_
       have hm:T≤T/δ:=le_div_self hT hD hV
       refine (add_le_add (mul_le_mul_of_nonneg_left hm (by positivity : 0≤ fingers 6^2*t^2)) (add_le_add (mul_le_of_le_one_right (by positivity) hh) (mul_le_of_le_one_right (by positivity) hh))).trans_eq (by unfold C; ring)
end YM.QCD.Entr.Meridian
#print axioms YM.QCD.Entr.Meridian.hires
