import YM.QCD.Lunar.Musk
import YM.QCD.Lunar.Cable
/-!
# Deterministic wrapping expansions at a fixed budget point
Uses finite equal distribution of minimum-cost pollen.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.High
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N k B n b j:ℕ}{p:BudgetPoint}{η u a r t w P q J δ z z' θ σ d A ε:ℝ}{i o:Site c}
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Entr Kites Lunar
variable {ι β:Type}
abbrev Pollen (k:ℕ)(o:Site c):= { p:Support c // o ∈ p ∧ ¬Nonwrapping p o ∧ coverNumber k p=tollV k c } -- parse ¬ scope!
lemma lived (h:c.val≥2): Nonempty (Pollen k o):=let hh:= artisan o k h; ⟨⟨hh.choose,hh.choose_spec⟩⟩
lemma seated (s:Strut c)(X: Support c): coverNumber k (X.image (act s))=coverNumber k X:= cover_map (Push.Local.turnSites s.1 s.2) (Push.Local.turn_sep s.1 s.2) ..
lemma stretchG (s:Strut c)(X: Support c)(o): Nonwrapping ((act s).finsetCongr X) (act s o) ↔ Nonwrapping X o:= by
    rw [show (act s).finsetCongr X=X.image (act s) from (by simp [map_eq_image])]; exact nonwrapping_turn (X:=X) s.1 s.2 o -- names
noncomputable def gild (s:Strut c)(j:ℕ)(o p:Site c)(h:p=act s o):Pollen j o ≃ Pollen j p:=Equiv.subtypeEquiv (act s).finsetCongr (fun X=> by
      change (_ ∧ _ ∧ _) ↔ p ∈ _ ∧ _ ∧ _; rw [h,(stretchG s X),show (coverNumber j ((act s).finsetCongr X))=coverNumber j X from (by rw [show (act s).finsetCongr X=X.image (act s) from (by simp [map_eq_image])]; apply seated)]
      simp -- edit
   )
variable (G:Gem c N ι)(b: Flavor N)
abbrev Field (G:Gem c N ι)(k:ℕ):= Σ i:ι,Pollen k (G.addr i).site
noncomputable def salve (v:Field G k):ℝ:= (Fintype.card (Pollen k (G.addr v.1).site):ℝ)⁻¹
noncomputable def air (k:ℕ):Gem c N (Field G k):= ⟨fun v=> ⟨(G.addr v.1).site,(G.addr v.1).support ∪ v.2.val,mem_union_left _ (G.addr v.1).anchor⟩, fun i=> salve G i • G.view i.1⟩ -- salve sig G explicit?
lemma feeds (t:ℕ)(hp:Crossing G):Crossing (air G t):=by
    let X:=air G t; constructor
    · refine ⟨fun i A k=>(clock G (salve G i) hp).blank.gauge i.1 A k,fun i A=>(clock G (salve G i) hp).blank.num i.1 A,fun i A=>(clock G (salve G i) hp).blank.real i.1 A⟩
    intro s k d he; obtain ⟨e,hQ⟩:= hp.rays s k d he; let M:= fun i=> gild s t (G.addr i).site (G.addr (e i)).site (congr_arg _ (hQ i).1); refine ⟨Equiv.sigmaCongr e M,?_⟩
    rintro ⟨i,T⟩; constructor
    · let D:=G.addr i; change ⟨_,(G.addr (e i)).support∪(M i T).val,_⟩=(⟨_,(D.support∪ T.val).image (act s),_⟩:RegularAddress c)
      congr 1; · exact congr_arg RegularAddress.site (hQ i).1
      rw [image_union,show (G.addr (e i)).support= _ from congr_arg RegularAddress.support (hQ i).1,show (M i T).val=T.val.image (act s) from ?_] -- motive
      · rfl
      · simp [M,gild,map_eq_image]
    intro V; change Diode _ _ _ _ (salve G (⟨i,T⟩:Field G t) • G.view i _)=salve G (⟨e i,M i T⟩:Field G t) • G.view (e i) V
    rw [eSM _ (phare _),(hQ i).2]; apply congr_arg₂; · unfold salve; simp only [← Fintype.card_congr (M i)] -- edit
    rfl
lemma noX (k:ℕ)(v:Field G k):¬Nonwrapping ((air G k).addr v).support ((air G k).addr v).site:= fun h=> v.2.2.2.1 (fun x hx=> h x (mem_union_right _ hx))
variable [Fintype ι]
lemma pours (k:ℕ) (hc:2 ≤ c.val)(i:Grid c): (∑ j,(air G k).view j i)=∑ j,G.view j i:=by
   rw [Fintype.sum_sigma]; apply sum_congr rfl; intro j _; haveI:Nonempty (Pollen k (G.addr j).site):=lived hc
   unfold air salve; change ∑ _ : Pollen k (G.addr j).site,(Fintype.card (Pollen k (G.addr j).site):ℝ)⁻¹ • G.view j i= G.view j i; rw [sum_const,card_univ,← Nat.cast_smul_eq_nsmul ℝ, smul_smul]; rw [mul_inv_cancel₀ (show (Fintype.card (Pollen k (G.addr j).site):ℝ) ≠0 from Nat.cast_ne_zero.2 Fintype.card_ne_zero),one_smul]
lemma flight (hz:0≤ σ)(hc:2 ≤ c.val)(h:AnchorT G p a σ u) : AnchorT (air G p.B) p a σ (Φ p.B σ c*u):=by
    let F:=air G p.B; obtain ⟨f,hp,hQ⟩:=h.peg
    have he (j :Field G p.B): (coverNumber p.B (F.addr j).support:ℝ) ≤ coverNumber p.B (G.addr j.1).support+tollV p.B c:=by
         have hp : coverNumber p.B (F.addr j).support ≤ coverNumber p.B (G.addr j.1).support+tollV p.B c:=(Corona.meets_sum (G.addr j.1).anchor j.2.property.1 p.B).trans_eq (congr_arg _ j.2.property.2.2); exact_mod_cast hp
    refine ⟨fun j=> ‖salve G j‖*f j.1,fun i=>?_ , fun i=> ⟨((hQ i.1).1.byScalar (salve G i)).stretches (subset_union_left) le_rfl,fun U=>?_⟩⟩
    · refine ⟨fun j=> ite_nonneg (mul_nonneg (mul_nonneg (norm_nonneg _) (hQ _).1.travel) (Real.exp_pos _).le) le_rfl,Summable.of_finite, ?_⟩
      apply le_trans _ (mul_le_mul_of_nonneg_left (hp i).2.2 (Real.exp_pos _).le); rw [tsum_fintype,tsum_fintype,Fintype.sum_sigma,Finset.mul_sum]; apply sum_le_sum; intro j _; by_cases hv:(G.addr j).site=i
      · rw [if_pos hv]
        let c':= Fintype.card (Pollen p.B (G.addr j).site); haveI:Nonempty (Pollen p.B (G.addr j).site):=lived hc; let k:ℝ:=c'; let W:= Real.exp (σ*coverNumber p.B (G.addr j).support); let v:=Φ p.B σ c*(f j*W); have hK:0<k:=by unfold k c'; positivity
        apply le_trans (b:=∑ _:Pollen p.B (G.addr j).site,k⁻¹*v) (sum_le_sum (fun r _=>?_))
        · rw [sum_const,card_univ,nsmul_eq_mul]; rw [show ↑(Fintype.card (Pollen _ _))= k from rfl]; rw [mul_inv_cancel_left₀ hK.ne']; -- edit
        · rw [if_pos (show (F.addr ⟨j,r⟩).site=i from hv)]; dsimp only; rw [show ‖salve G (⟨j,r⟩:Field G p.B)‖=k⁻¹ from Real.norm_of_nonneg (inv_nonneg.mpr hK.le)]; apply le_trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (he ⟨j,r⟩) hz)) (mul_nonneg (inv_nonneg.mpr hK.le) (hQ j).1.travel)); unfold v W Φ; rw [mul_add,Real.exp_add]; exact Eq.le (by ring)
      unfold air; simp [hv]
    let W:=G.addr i.1; rw [← measures]; change ‖needle W.site N a (salve G i • G.view i.1 U)‖≤_; rw [show needle W.site N a (salve G i • G.view i.1 U)= _ from (map_smul ((needle W.site N a).restrictScalars ℝ) (salve G i) (G.view i.1 U)),norm_smul] -- edit
    exact mul_le_mul_of_nonneg_left (by change ‖needle W.site N a _‖ ≤_; rw [measures]; exact (hQ _).2 _) (norm_nonneg _)
end YM.QCD.High
