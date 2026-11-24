import YM.Helio.Ribbons
import YM.Helio.Gate
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
variable (G:Silo c)
variable (x:Axis)(d:Tick c)
local notation "R"=>strip x d
local notation "L"=> newDay x d G
variable {Z:ℝ}
variable (hZ: CreditBeam Z)(hq:Run.Pack id id η δ B U q G A)(hv:Torch G)
open Push.Uniform WardBin.Lies Metric
local notation "χ" i:arg=> weighT i A x
lemma flatClaws (hv:0<η)(ht:Run.Pack id id η δ B U q G A)(hd:Torch G): L 1=0:=by
    have he : overlayP x (1:Grid c)=1:=by
       ext1 e; rw [show overlayP x (1:Grid c) e=(1:Grid c) (e.1,x)*sky (rplus c x) (1:Grid c) e*((1:Grid c) (e.1+step e.2,x))⁻¹ from rfl,show sky _ _ e = _ from pullR (1:Grid c) x e.2 e.1]; simp
    rw [penny _ x d G ht hd, he, sub_self, zero_mul]
lemma zeroRoute (hq:Run.Pack id id η δ B U q G A)(hv: ¬fertile d)(ht:0<η): L=0:= by
    funext V; unfold newDay; rw [debtless hq _ V (mt (scripture x d).2 hv) ht,debtless hq _ V hv ht,mul_zero,zero_mul,sub_zero]; rfl
structure HighBar (p: Site c)(f:Support c)(P:BudgetPoint)(x:Grid c→Bundle)(M J:ℝ):Prop where
    nn : 0 ≤ M
    nj : 0 ≤ J
    scope : LocalOn f x
    core (U:Grid c) : ‖x U‖ ≤ M
    fee (U:Grid c)(h:Healthy P.threshold f U) (o:Site c)(ht:o∈f)(l:List (Directions su c))(hn:l.length≤P.order)(he:∀ i∈l,P.dirBound o i) : ‖leftDerivs x l U‖*(1+(separation o p:ℝ))^2≤J
    smooth (U:Grid c)(n:ℕ) : Push.Local.Chart n x U
    continuous: Continuous x
-- maybe fee separation want for end x,y, and global.M adjust
variable {Y: Type}
lemma magnet (n b B:ℕ)(hZ:CreditBeam Z): ∃ C:ℝ,0 ≤ C ∧∀(c:Side)(x:Axis)(U:St c)(η δ q:ℝ)(G:Silo c)(A:BankP c), Run.Pack id id η δ B U q G A → Torch G→ ∀ (p:BudgetPoint),p.power≤b→p.order ≤ n→p.threshold ≤η→ Z*p.threshold < η/2→η≤1→∀ i:Tick c,fertile i → let D:=strip x i; let a:= C*basePrice A x i; let W:= a*tribute B b n D
    let F:=newDay x i G; HighBar i.1 D p F a (W*(p.threshold/η)) ∧
      ∀ (o:Site c),o∈D → (∀ V:Grid c,‖F V‖ *(1+(diameterQ B D:ℝ))^2≤ W) ∧∀(V:Grid c)(h:Healthy p.threshold D V) (l:List (Directions su c)), l.length ≤ p.order → (∀ i∈l,p.dirBound o i) → ‖leftDerivs F l V‖*(1+(diameterQ B D:ℝ))^2≤ W*(p.threshold/η):=by
    obtain ⟨C,hC,h⟩:=polarBudget n b B; let K:ℝ:=(C+1)*(1+‖TouchL‖*2)+Z*2; have hZ₀:=hZ.ticket; have hK:0≤ K:=by unfold K; positivity
    refine ⟨K,hK,fun c x U η δ q G A hp ht p hP hM hv hE hΩ i hf=> ?_⟩; intro D a W F
    let X:= basePrice A x i; let γ:= weighT i A x; let r:= p.threshold/η; let Y:Pulse c→Bundle:=novaB x i G; let z:= p.threshold; let d:ℝ:= diameterQ B D
    have ha:=p.threshold_pos; have hh:=ha.trans_le hv; have hu:0<r:=div_pos ha hh; have hz:=need hp i; have hω : silos A i≤ X:=le_add_of_nonneg_right (need hp _);
    have hx:= hz.trans hω; have hy:D=D:=rfl
    have hδ:= Nat.cast_nonneg (α:=ℝ) (diameterQ B D); have hc: 1 ≤ 1+d:= le_add_of_nonneg_right hδ; have hγ: γ=‖TouchL‖*2 * X :=by unfold γ weighT; unfold X basePrice; ring
    have hw: W=a*((1+d)^(b*n)*(1+d)^2):=by unfold W tribute; rw [add_comm (2:ℕ), pow_add]
    have ha' :0 ≤ a:= mul_nonneg hK hx; have he:C*γ ≤ a:=by rw [hγ]; unfold a K; change C* _ ≤ _*X; nlinarith only [mul_nonneg (norm_nonneg TouchL) hx,ha',hx,mul_nonneg (hZ₀.le) hx,mul_nonneg hC hx]
    have he' : γ≤ a:=by rw [hγ]; apply mul_le_mul_of_nonneg_right _ hx; unfold K; nlinarith only [show 0 ≤ ‖TouchL‖ from norm_nonneg TouchL,hZ₀,hC, mul_nonneg hC (norm_nonneg TouchL)]
    have he'' : silos A i*(Z*2) ≤ a:=by unfold a; apply (mul_le_mul_of_nonneg_right hω (by positivity)).trans; rw [mul_comm]; apply mul_le_mul_of_nonneg_right _ hx; unfold K; simp only [le_add_iff_nonneg_left]; positivity
    have hF : F=Y ∘ settled:= funext (fun V=> (earnedT V x i G).symm)
    have hNp := novaCost x i G hp hf hh hΩ; have hm (V:Grid c): ‖F V‖ ≤ a:=by rw [hF]; exact (hNp.2.2.2.1 _ (citizenship c hh V)).trans he'
    have hl (o:Site c)(ho:o∈D)(V:Grid c): ‖F V‖*(1+d)^2 ≤ W:=by
       apply (mul_le_mul_of_nonneg_right (hm V) (sq_nonneg _)).trans; rw [hw]; apply mul_le_mul_of_nonneg_left _ ha'; exact le_mul_of_one_le_left (sq_nonneg _) (one_le_pow₀ hc)
    have hJ (o:Site c)(ho:o∈D)(V:Grid c)(hv':Healthy z D V)(l:List (Directions su c))(hd:l.length ≤ p.order)(he₁:∀ i∈l,p.dirBound o i): ‖leftDerivs F l V‖ ≤ a*(1+d)^(b*n)*r:=by
       by_cases htL:l=[]; · subst l; apply (usesP G x i hZ hp ht V hv' hh hE).trans; exact mul_le_mul_of_nonneg_right (he''.trans (le_mul_of_one_le_right ha' (one_le_pow₀ hc))) hu.le
       rw [hF]; apply (h c D p Y o η γ _ _ hNp ho hP hM hv hΩ l htL hd he₁ V).trans; rw [mul_comm a]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (pow_nonneg (zero_le_one.trans hc) _)) hu.le
    have hℓ o ho V h l hd he : ‖leftDerivs F l V‖*(1+d)^2≤ W*r:= (mul_le_mul_of_nonneg_right (hJ o ho V h l hd he) (sq_nonneg _)).trans_eq (by rw [hw]; ring)
    refine ⟨⟨ha', ?_,hF.symm ▸ hNp.2.2.2.2.1,hm,fun V h o ho l hd he=>?_,fun V n=>hF.symm ▸ milady hNp hh V n,hF.symm ▸ breeze hNp hh⟩,fun o ho=>⟨hl o ho,?ctor⟩⟩
    case ctor => exact fun V h l hd he=>hℓ o ho V h l hd he
    · apply mul_nonneg _ hu.le; rw [hw]; positivity
    exact (mul_le_mul_of_nonneg_left (show _ ≤ (1+d)^2 from pow_le_pow_left₀ (by positivity) (by gcongr; exact Nat.cast_le.mpr (Corona.extent D B ho (primeM x i hf).1)) 2) (norm_nonneg _)).trans (hℓ o ho V h l hd he)
end Meridian
end YM.QCD.Entr
#print axioms YM.QCD.Entr.Meridian.magnet
