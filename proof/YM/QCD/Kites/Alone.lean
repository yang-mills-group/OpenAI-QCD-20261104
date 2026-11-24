import YM.QCD.Kites.Speed
/-! # speed fits charges before next RG support; don't make uncalibrated blocks -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Kites
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N k B n b j:ℕ}{p:BudgetPoint}{η u a r t w P q J δ z z' θ σ d A ε:ℝ}{i o:Site c}
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Pine YM.Next.Free Leaf LeafM Tee Garden Entr
variable {Γ:Silo c}{U:St c}{ι β ν:Type}
local notation "V"=> EvenA c N
variable (G:Gem c N ι)(F:Rail c N β)
structure Quits (F:Rail c N β)(B:ℕ)(W R A r:ℝ) :Prop where
 cost : ∃ f:β→ℝ, Ac.Hit (Ruby.home F) B (GasP.taxed (Ruby.oriD F) f R) A W ∧ ∀ i x, ‖token c N r (F.warp i x)‖ ≤ f i
noncomputable def flightE (k:ℝ): Gem c N ι:=⟨G.addr,fun i U=> wearK c N k (G.view i U)⟩
noncomputable def flightK (k:ℝ):Rail c N β:=⟨F.addr,fun i U=> wearK c N k (F.warp i U)⟩
lemma purity (U: Matrix (Modes c N) (Modes c N) ℂ)(x:V)(t:ℝ): sways U (wearK c N t x)=wearK c N t (sways U x):=Subtype.ext (pitcher U x.val t)
lemma dearR (x:EvenA c N)(t:ℝ): Regal c N (wearK c N t x)= wearK c N t (Regal c N x):=by
    apply Subtype.ext; change disguise (idol c N) (surf (Modes c N) (engine t _ x.val))= engine t _ (disguise (idol c N) _); rw [surfE,pitcher]; rfl
lemma dry_stage (E: Grid c→EvenA c N)(p:ℝ)(h:shadeG E)(hv:∀ i,Fit (E i))(ht:∀ i,Regal c N (E i)= E i) (Vw:Grid c):
    let f:= wearK c N p ∘ E; shadeG f ∧ Fit (f Vw)∧ Regal c N (f Vw)=f Vw := by
    intro f; refine ⟨?_,fun W hp=> ?_, ?_⟩
    · intro U k; have hg:sways (Lat.rotates N k) (E (Lattice.gauge k U))=E U:=Subtype.ext (h U k)
      exact congr_arg Subtype.val ((purity (Lat.rotates N k) (E (gauge k U)) p).trans (congr_arg (wearK c N p) hg))
    · exact (purity (flute (Lat.Row c) W) (E Vw) p).trans (congr_arg _ (hv Vw _ hp))
    exact (dearR (E Vw) p).trans (congr_arg _ (ht Vw))
lemma gustE (h:Crossing G)(r:ℝ): Crossing (flightE G r):=by
    have he i:=dry_stage (G.view i) r (h.blank.gauge i) (h.blank.num i) (h.blank.real i); refine ⟨⟨fun i=> (he i 1).1,fun i W=> (he i W).2.1,fun i W=> (he i W).2.2⟩,?_⟩
    intro s k d hv; obtain ⟨e,hp⟩:=h.rays s k d hv; exact ⟨e,fun i=>⟨(hp i).1,fun W=>(purity _ _ r).trans (congr_arg (wearK c N r) ((hp i).2 W))⟩⟩ -- purity arguments
lemma gustK (h:MixedP F)(hp:F.Reg t)(r:ℝ): let Z:=flightK F r; Z.Reg t∧ MixedP Z:=by
    intro Z; have he i:=dry_stage (F.warp i) r (h.gauge i) (h.num i) (h.real i); refine ⟨⟨fun i U W hv hq=>?_,fun i=>?_,fun i W=> dings r _ _ (hp.role ..),fun i U hx=> hp.buys i U (fun hw=>hx ?_)⟩,⟨fun i=>(he i 1).1,fun i U=> (he i U).2.1,fun i U=>(he i U).2.2,?_⟩⟩
    · exact congr_arg (wearK c N r) (hp.uses i U W hv hq)
    · exact (songT (c:=c) (N:=N) r).continuous.measurable.comp (hp.reads i)
    · exact (congr_arg _ hw).trans (map_zero (wearK c N r))
    intro s d k hv; obtain ⟨e,hv⟩:= h.moves s d k hv; refine ⟨e,fun i=>⟨(hv i).1,(hv i).2.1,fun j=>(purity _ _ _).trans (congr_arg (wearK c N r) ((hv i).2.2 j))⟩⟩
lemma proofM (t:ℝ)(x:V): mud (wearK c N t x)=mud x:=by change coef ∅ (engine t _ x.val)=_; rw [show coef ∅ (engine t _ x.val)=_ from fundW x.val t ∅,card_empty,pow_zero,one_mul]; rfl
lemma proofR (t:ℝ)(x:V): river c N (wearK c N t x)=river c N x:=by change -(mud _).re= -(mud _).re; rw [proofM]
lemma proofW (t:ℝ)(x:V) (b: Flavor N): meter b (wearK c N t x)= (t:ℂ)^2 • meter b x:=by
    ext i j; change _*coef (tag _ _) (engine _ _ x.val)=_; rw [fundW]; have hh (i j:Modes c N): (Stew.tag i j).card=2:=by simp [Stew.tag]
    rw [hh, mul_left_comm]; rfl
lemma pears (t:ℝ)(b:Flavor N)(hp:Quartz G)(he:Quanta G b): Quartz (flightE G t)∧ Quanta (flightE G t) b:=by
    refine ⟨⟨fun i=> (proofM ..).trans (hp.face i),fun i hx x y hz hv=>?_⟩,fun i h q=>?_⟩
    · rw [show ((river c N) ∘ (flightE G t).view i)=_ from (show _=river c N ∘ G.view i from funext fun U=>proofR _ _)]; exact hp.van i hx x y hz hv
    change profile (G.addr i).site q (meter b (wearK c N t (G.view i 1)))=_; rw [proofW,map_smul,show profile _ _ (meter b (G.view i 1))=0 from he i h q, smul_zero] -- defeq
lemma excess (h: Quits F B w ε r t)(hv:0< a)(hx:0<η)(he:η*a ≤ t): Quits (flightK F η) B w ε r a:=by obtain ⟨f,hf,h⟩:=h.cost; exact ⟨f,hf,fun i U=>(quy _ _ _ _ hx hv he).trans (h _ _)⟩
lemma irises (h: Licence p w P t G)(hv:0≤ a)(hx:0≤η)(he:η*a ≤ t): Licence p w P a (flightE G η):=by
    obtain ⟨f,hf,h⟩:=h.zone; let X:=wearK c N η; refine ⟨f,hf,fun i=>?_⟩; obtain ⟨hr,hg,hQ,hz,hV,hP⟩:= h i
    let Y (Vv:Grid c):= G.view i Vv; let A := songT (N:=N) (c:=c) η
    change Woven _ _ _ _ (A ∘ Y) _; refine ⟨fun U Xw hh=> congr_arg A (hr U Xw hh),fun Vw=> dings η _ _ (hg _),fun Vw hv=>(A.contDiff.contDiffAt.comp 0 (hQ Vw hv)), ?_, A.continuous.measurable.comp hV,hP⟩
    intro Vw hh x hx' hc; rw [Push.Local.left_linear A x (hQ Vw hh) hx']; rw [show A _=X _ from rfl]; rw [show Sen _ _ (X _)=_ from moments η a _ _ hv hx]; exact (future _ (mul_nonneg hx hv) he _).trans (hz _ hh x hx' hc)
lemma sour (U:Grid c)(t:ℝ)(h:Summable (letters G p.threshold U)):HasSum (letters (flightE G t) p.threshold U) (wearK c N t (Patron.total G p.threshold U)):=by
    apply ((songT t).hasSum h.hasSum).congr_fun; intro i; exact sprayer p.threshold (G.addr i).support (G.addr i).support (G.view i) U U (wearK c N t).toRingHom ((flightE G t).view i) Iff.rfl rfl|>.symm
lemma story (U:Grid c)(t:ℝ)(T:ℝ)(h:Summable (Ruby.tK F T U)): HasSum (Ruby.tK (flightK F t) T U) (wearK c N t (∑' i,Ruby.tK F T U i)):=by
    apply ((songT t).hasSum h.hasSum).congr_fun; intro i; unfold Ruby.tK; split; next hx=> rw [if_pos (show separated (blocked (Ruby.home F)) i ∧ flags T U=i.biUnion (Ruby.oriD F) from hx)]; exact (map_prod (wearK c N t) ..).symm
    next hx=> rw [if_neg (show ¬(separated (blocked (Ruby.home F)) i ∧ flags T U=i.biUnion (Ruby.oriD F)) from hx)]; exact (map_zero (wearK c N t)).symm
end YM.QCD.Kites
