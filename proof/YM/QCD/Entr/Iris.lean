import YM.QCD.Entr.Blue
/-! # exact exponent extraction of both Lie components. Holding clocks. pending numeric restorations -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Entr
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N k B n b j:ℕ}{p:BudgetPoint}{η u a r t w P q J δ z z' θ σ d A ε:ℝ}{i o:Site c}
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Pine YM.Next.Free Leaf LeafM Tee Garden
variable {Γ:Silo c}{U:St c}
variable {ι β ι':Type}(G:Gem c N ι)(F:Gem c N β)(b:Flavor N)
lemma joinsM {H H':ℝ}(B':Ruby.Hue c N β)(F':Ruby.Hue c N ι)(h: Purchases B' p.threshold p.B u H a)(ht:Purchases F' p.threshold p.B u H' a):Purchases (Ruby.HJoin B' F') p.threshold p.B u (H+H') a:=by
    obtain ⟨f,hf,h'⟩:= h.paint; obtain ⟨g,hg,hM⟩:= ht.paint; exact ⟨Ruby.nestling B' F' h.projection ht.projection,Ruby.branche B' F' h.life ht.life,Sum.elim f g,fun i U=>by cases i; exact hf _ _; exact hg _ _,fun i=> Extra.Iteration.Cost.sum (h' i) (hM i)⟩
lemma firmsM (B':Ruby.Hue c N β)(F':Ruby.Hue c N ι)(x y:EvenA c N)(V:Grid c)(hp: HasSum (fun i=>B'.mean i V) x)(ht: HasSum (fun i=>F'.mean i V) y): HasSum (fun i=>(Ruby.HJoin B' F').mean i V) (x+y):=HasSum.sum (f:=fun i=>(Ruby.HJoin B' F').mean i V) hp ht
variable [Countable ι] [Fintype β]
open Collection Extra.Iteration Averaging WilsonStartup
local notation "Y"=> fiscal G F (legA G F b) (legϑ G F b)
noncomputable def charm := Stew.dearth (Y) b
local notation "E"=> charm G F b
noncomputable def betaP :ℝ:= Averaging.delta ((theater (E)).read (stock (E)))
local notation "T"=> theater (E)
local notation "d0"=> betaP G F b
variable {R:PathData su}{c':Clip}
noncomputable abbrev library (R: PathData su)(c':Clip)(p:BudgetPoint)(α:ℝ):= fill (T) R c' p (stock (E)) α (d0)
noncomputable abbrev pharmacy (R: PathData su)(p:BudgetPoint):= shelves (T) R p
noncomputable abbrev tele (R: PathData su)(c': Clip)(p:BudgetPoint)(θ:ℝ):= weave (wade (E)) (ostinato (pharmacy G F b R p) (library G F b R c' p θ) N)
noncomputable abbrev envy (R:PathData su)(c':Clip)(p:BudgetPoint)(θ:ℝ):=Ruby.HJoin (offT (elog F (legA G F b) (legϑ G F b)) p.threshold) (Ruby.HJoin (lien (Y) b p.threshold) (riff (pharmacy G F b R p) (library G F b R c' p θ) N)) -- gotta alpha implicit
-- wealth supplies. maintain precision hull
abbrev lower (L P t:ℝ)(p:BudgetPoint)(N:ℕ):=(P+widthμ (Quotes.preExponent p) N)*(L*t)
noncomputable abbrev scoreT (M H:ℝ)(p:BudgetPoint):= (1+M)*Real.exp (81*Quotes.preExponent p)*H
lemma hikes (W:Ruby.Hue c N ι)(h: Purchases W p.threshold p.B r P a)(he:P≤q):Purchases W p.threshold p.B r q a:= by obtain ⟨f,hf,hQ⟩:=h.paint; exact ⟨h.projection,h.life,f,hf,fun i=> Extra.Iteration.Cost.enlarge (hQ i) he⟩
lemma scoreH (G:Gem c N ι)(h:Licence p r t a G)(he:t≤w):Licence p r w a G:=by obtain ⟨f,hf,hV⟩:=h.zone; exact ⟨f,fun i=> Extra.Iteration.Cost.enlarge (hf i) he,hV⟩
omit [Countable ι] in
-- MISSING measurable & real pull after post. Cost scalings.
lemma hector (hP:0≤q)(hv:t≤w): payment 1 k n 1 1 t q 0 ≤ payment 1 k n 1 1 w q 0 :=by unfold payment degreeIncome; gcongr <;> first| positivity| refine inv_nonneg.mpr (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith)))
-- installed conservation pre-K price, **complete signature solving** assuming previous values not claimed supplied. 
lemma kinetic (N R n:ℕ) (P:ℝ)(hP:1≤P):∃ L M:ℝ,1≤L∧1≤ M∧∀ (c: Side) (U:St c)(p:BudgetPoint)(v:Clip)(W:PathData su)(A η C r:ℝ), n≥p.order → R ≥ p.power→p.B ≥ 2→ 20<c.val → W.Bounds v η C A → Decent v p→Geo.Width p v η→∀ (ι β:Type)[Countable ι][Fintype β],∀ (G:Gem c N ι)(F:Gem c N β)(t a:ℝ)(b:Flavor N), 1 ≤ a →Crossing G→ Licence p (Quotes.preExponent p) t a G → SlotT F p a (Quotes.preExponent p) P U →
     let X:= tele G F b W v p r; let V:=envy G F b W v p r; let d:= betaP G F b; let Z:=charm G F b
     let u:=scoreT M (t+lower L P t p N) p; let hw:=p.supportExponent+1; let S:= payment 1 (4*p.B+2) 0 1 1 (lower L P t p N) hw 0 + (payment 1 (4*p.B+2) 0 1 (1+M) (t+lower L P t p N) hw 81+softNeed su p v η C r u)
     a^2*|legϑ G F b| ≤ L*t∧ a^2*|legA G F b|≤ L*t∧ Quanta X b ∧ Quartz X∧ Crossing X∧ Licence p p.supportExponent (2*u+regularNeed su p v η C r u) a X ∧ p.threshold^2 *|d|≤u ∧ Purchases V p.threshold p.B hw S a ∧∀ x:Grid c,∀ β τ:ℝ, HasSum (fun i=> V.mean i x) (baker c N (pulse W v p β τ x-r*receipt W v p x)+Patron.total G p.threshold x - ((nozzle c N (legϑ G F b • U x+legA G F b • (1:Sheet c)))+Patron.total X p.threshold x + baker c N (pulse W v p (β+r+d) (vac (stock Z) τ) x))) :=by
    obtain ⟨L,hL,H⟩:=shooting N P hP
    obtain ⟨K,M,hK,hM,H'⟩:= Stew.wealth n R N
    refine ⟨L,M,hL,hM,fun c U p v W R' η C α hv he hB hn hW ht hx ι β _ _ G F t a b hb h hQ hF=> ?_⟩; intro X V d Z u hw S; let σ:= Quotes.preExponent p
    have hs := p.exponent_pos; have he' :0 ≤ hw:=by unfold hw; linarith
    have hk : hw+1+1≤ σ :=by unfold hw σ Quotes.preExponent; linarith
    have hz : 0 ≤ σ:=by linarith
    have hI:= zero_lt_one.trans_le hb; let e:=legϑ G F b; let m:=legA G F b; let P':= fiscal G F m e; obtain ⟨hl,hA⟩:= H _ _ _ G F p U a σ t hI hz hF hQ b; let D:=(|e| *P+|m| * widthμ σ N)*a^2
    have hY: D ≤ lower L P t p N:=by unfold D lower; unfold e m σ; linarith only [mul_le_mul_of_nonneg_right hl (zero_le_one.trans hP),mul_le_mul_of_nonneg_right hA (μworth (σ:=σ) (N:=N))] -- need unfold
    obtain ⟨hD,hS,hC,hJ,hR,hVS⟩:=settles G F b hF hQ hI hz h hk he'
    have hP': Licence p σ (t+lower L P t p N) a P':=scoreH P' hJ (by exact add_le_add_right hY t)
    obtain ⟨hZ,hX,hc,hf,hp,ha,hg⟩:= H' c p σ hw a (t+lower L P t p N) he' hk hB hv he hb (by omega) _ P' b hC hP'
    obtain ⟨hZ',hX',hf',hY',hg',hV,hA'⟩:= tune Z b hZ hX hI hW ht hx hn hf (α:=α)
    refine ⟨hl,hA,hX',hZ',hf',hY',hV, joinsM _ _ (hikes _ hR (hector he' hY)) (joinsM _ _ hc hg'),fun x β τ=> ?_⟩
    have hh:= firmsM _ _ _ _ x (hVS x) (firmsM _ _ _ _ x (hg x).2.2 (hA' x β τ)); change HasSum (fun i=> V.mean i x) (_+(_+_)) at hh
    have hr: ∀ W:Grid c,paleF N (backP (till P' b 0) W)=0:=by intro W; unfold backP; rw [hD,hS]; simp only [Complex.ofReal_zero,zero_smul,add_zero]; exact map_zero (nozzle _ _) -- use map_zero
    -- char notation
    rw [hr] at hh
    change HasSum _ ((Patron.total G p.threshold x-(nozzle c N _+Patron.total P' p.threshold x))+ (Patron.total P' p.threshold x -0-Patron.total Z p.threshold x + ((baker c N (pulse W v p β τ x-α*receipt W v p x)) + Patron.total Z p.threshold x - (baker c N (pulse W v p (β+α+d) (vac (stock Z) τ) x)+Patron.total X p.threshold x)))) at hh
    abel_nf at hh ⊢; exact hh
end YM.QCD.Entr
