import YM.QCD.Kites.Term
/-! # publication under budgets. Keeps old unmasked spectator & alpha receipt. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Kites
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N k B n b j:ℕ}{p:BudgetPoint}{η u a r t w P q J δ z z' θ σ d A ε S A':ℝ}{i o:Site c}
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Pine YM.Next.Free Leaf LeafM Tee Garden Entr
variable {Γ:Silo c}{X:St c}{ι β ν α ι':Type}
local notation "V'"=> EvenA c N
variable (G: Gem c N ι)(F: Rail c N β)(Y: Ruby.Hue c N ν) (W:Gem c N α)(Y': Ruby.Hue c N ι')
lemma heart (h:Purchases Y p.threshold p.B r t a)(he:0≤ r)(ha:1≤a) (x:Grid c): Summable (fun i=> Y.mean i x) ∧ Summable (fun i=> ‖Ruby.sparkY Y x i‖):=by
    obtain ⟨u,hv,hU⟩:=h.paint; exact Ruby.hearts Y h.life hU (fun i=> (norm_nonneg _).trans (hv i 1)) ha he hv x
open Pressure Jets.Touch
noncomputable def priceK (L:Side)(M:ℝ)(x:ℝ):= Real.exp (Delay.hatWin su L (M/2) (1/2) x)
lemma bearK (L:Side)(M a:ℝ)(h:0 < M)(he:0≤a): ∀ᶠ x:ℝ in atTop, ∀ (c:Side)(N:ℕ)(ι β:Type)(Y:Ruby.Hue c N ι)(X:Rail c N β)(p:BudgetPoint)(t:ℝ), p.B=radiusB x → Quits X p.B 1 (priceK L M x) (a+1) t → Purchases Y p.threshold p.B (a+1+1) (pra L x) t → Quits (Ruby.Trail Y X p.threshold) p.B 1 (taxK L x 1) a t :=by
   filter_upwards [Ruby.portends L M a h he] with x hx; intro c N ι β Y X p t ht hp hz; obtain ⟨g,hg,hX⟩:=hp.cost; obtain ⟨y,hy,hY⟩:=hz.paint; rw [ht] at hY hg ⊢
   have he : 0≤ g:=fun i=> (norm_nonneg _).trans (hX i 1); have he':0≤y:=fun i=> (norm_nonneg _).trans (hy i 1); refine ⟨Ruby.fair Y X y g,?_ , fun i U=> Ruby.haloP Y X he' he hy hX i U⟩
   exact hx c N ι β Y X y g p.threshold t he' he hy hX hg hY
lemma scant (h: Purchases Y p.threshold p.B r A a) (hz:u≤ r)(hp:A≤ t): Purchases Y p.threshold p.B u t a:=by
    obtain ⟨f,hf,hH⟩:=h.paint; refine ⟨h.projection,h.life,f,hf,fun i=> Extra.Iteration.Cost.enlarge ?_ hp⟩; apply Extra.Iteration.Cost.mono (hH i)
    · intro j; split; exact mul_nonneg ((norm_nonneg _).trans (hf j 1)) (Real.exp_pos _).le; exact le_rfl
    intro i; split; next h=> exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right hz (Nat.cast_nonneg _))) ((norm_nonneg _).trans (hf i 1))
    next _=> exact le_rfl
abbrev codE (D:St c)(ρ m:ℝ): St c:=ρ • D+m • 1
abbrev tank (u: Grid c→ℝ)(p:PathData su) (v:Clip)(R:BudgetPoint)(β τ:ℝ):= fun x:Grid c=> pulse p v R β τ x + u x
lemma accept (U:Grid c) {G':Gem c N ι'} (v u:Grid c→ℝ)(X:St c) (x y:ℝ) : heartS G S v X U - heartS G' S u (codE X (1+x) y) U=(baker c N (v U)+Patron.total G S U)- (nozzle c N (x • X U+y • 1) +Patron.total G' S U +baker c N (u U)):=by
   unfold heartS codE; simp only [Pi.add_apply, Pi.smul_apply,Pi.one_apply, add_smul,one_smul,map_add]; abel
lemma stationed {G':Gem c N ι'}(X:St c)(v u:Grid c→ℝ)(x y:ℝ)(hp:Y.Tall p.threshold)(hz:Purchases Y p.threshold p.B r A a) {ωx:Type}(Y':Ruby.Hue c N ωx) (h: Purchases Y' p.threshold p.B r A' a)
    (he:0 ≤ r)(hv:1≤a)(hU:∀ U: Grid c, HasSum (fun i=>Y'.mean i U) ((baker c N (v U)+Patron.total G p.threshold U)- (nozzle c N (x • X U+y • 1) +Patron.total G' p.threshold U+baker c N (u U))))(hf: ∀ U,Summable (Ruby.tK F p.threshold U))(ht:Licence p σ J t G')(hw:0< t)(hS:0≤σ) (s:ℝ) (hs:s^2*(1+x)=1) :
    let T:=Ruby.Trail (Ruby.HJoin Y Y') F p.threshold
    let E:=flightE G' s; let H:=flightK T s
    ∀ U,wearK c N s (scoreX G F Y p.threshold v X U)=scoreV E H p.threshold u (X+(s^2*y) • 1) U :=by
    intro T E H U; have he' : Purchases (Ruby.HJoin Y Y') p.threshold p.B r (A+A') a:= joinsM _ _ hz h; obtain ⟨hf',hZ⟩ :=heart _ he' he hv U
    have hR := Ruby.plenary _ F U (hf U) he'.life hf' hZ
    rw [sunI F G Y Y' he'.life v u X (codE X (1+x) y) G' U (hf U) (by rw [accept]; exact hU U) hZ (heart _ hz he hv U).1]; rw [eff _ T U s p.threshold u _ hR.summable (permits _ ht hw hS _) rfl]; congr 1; unfold codE; rw [smul_add,smul_smul,hs,one_smul,smul_smul] -- defeq
end YM.QCD.Kites
