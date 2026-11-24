import YM.QCD.Stem.Proof
/-! # Exemption α compiled. stubs. Includes proof book station formal.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Stem
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun Kites
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {I J V:Type}{c f:Side}{N n:ℕ}
open Animals Flume Orbit Quarry Folding Further.PhysicalPeriodLimitF933 Macrame PhysicalNext.Repeat Deck Meadow
open Pressure Precision ConnectedActivityE6 Blaze King Push.Uniform
open Brick Dust Grove AnalyticBridge VerifiedReset
variable {C:Side}{D D' w j:ℕ}{d r t t' p p' η b z A Δ θ ρ P':ℝ}{B:BudgetPoint}
open Entr Villa Port Fork Grove YM.Next.Scheduling Footprint Moss Extra.Iteration
variable (S:Gem c N I)(X:Finset I)(G:Gem c N J)(V':Ruby.Hue c N V)
noncomputable def renS (k:ℝ): Gem c N I:=⟨S.addr,fun i=> k • S.view i⟩
noncomputable def renV (k:ℝ): Ruby.Hue c N V:= ⟨V'.bud,fun i=>k • V'.mean i⟩
lemma payable (x:I→ℝ)(k:ℝ)(h:Anchored (fun i=>(S.addr i).site) x (fun i=>coverNumber n (S.addr i).support) t d): Anchored (fun i=> (S.addr i).site) (‖k‖ • x) (fun i=>coverNumber n (S.addr i).support) t (‖k‖*d):=by
   intro i; let u:=budget_scale (norm_nonneg k) (h i); convert u using 2 with j; dsimp only [Pi.smul_apply,smul_eq_mul]; split<;> ring
lemma scales (h : Licence B t d r S)(k:ℝ):Licence B t (‖k‖*d) r (renS S k):=by obtain ⟨p,hp,h⟩:=h.zone; exact ⟨‖k‖ • p,payable _ _ _ hp, fun i=>(h i).byScalar k⟩
lemma topaz (h:Dyed S)(k:ℝ): Dyed (renS S k):=by
    refine ⟨fun i U g=> ?_,fun i U W hv=> ?_,fun i U=>?_⟩
    · exact congr_arg Subtype.val ((eSM (sways (Lat.rotates N g)) (phare _) k (S.view i (Lattice.gauge g U))).trans (congr_arg (k • ·) (show sways _ _=S.view i U from Subtype.ext (h.gauge i U g)))) -- universals
    · exact dated k _ (h.num i U) W hv -- arguments
    exact dolled k _ (h.real i U) -- maybe wrong
lemma breath (h:SoilB X S B w r)(k:ℝ): SoilB X (renS S k) B w r:=by
    refine ⟨fun i hi=>⟨_,((h.fees i hi).choose_spec).byScalar k⟩,h.tortillas,fun i hi U g=> ?_,fun i hi U=> dated k _ (h.fit i hi U),fun i hi U=>?_⟩
    · exact congr_arg Subtype.val ((eSM (sways (Lat.rotates N g)) (phare _) k (S.view i (gauge g U))).trans (congr_arg (k • ·) (show sways _ _=S.view i U from Subtype.ext (h.gauge i hi U g))))
    exact dolled k _ (h.real i hi U) -- edit
lemma pokes (h:Pockets X S B r d)(k:ℝ): Pockets X (renS S k) B r (‖k‖*d) :=by obtain ⟨x,hf,h⟩:=h.tokenEq; refine ⟨‖k‖ • x,fun i hi=> (hf i hi).byScalar k,fun i=>?_⟩; simp only [Pi.smul_apply,smul_eq_mul,← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (h i) (norm_nonneg _)
lemma tranquil (h:TokenB V' t w z d r)(k:ℝ): TokenB (renV V' k) t w z (‖k‖*d) r:=by
    obtain ⟨y,hy,hp⟩:= h.pay
    have he: Ac.Hit V'.bud w (‖k‖ • y) z (‖k‖*d):=by
       intro i; let u:= budget_scale (norm_nonneg k) (hy i); convert u using 2 with i; dsimp only [Pi.smul_apply,smul_eq_mul]; split<;>ring
    refine ⟨⟨fun i U V x y=>congr_arg (k • ·) (h.mask.bond i U V x y),fun i=> measurable_const.smul (h.mask.meas i),fun i U a=> h.mask.non _ _ (fun b=>a ((congr_arg (k • ·) b).trans (smul_zero _))),fun i V=>Territory.club _ _ _ (h.mask.lives i V)⟩,fun i U g=>?_,fun i U=> dated k _ (h.fit i U),fun i U=>?_,‖k‖ • y,he,fun i U=>?_⟩
    · exact congr_arg Subtype.val ((eSM (sways (Lat.rotates N g)) (phare _) k (V'.mean i (Lattice.gauge g U))).trans (congr_arg (k • ·) (show sways _ _=V'.mean i U from Subtype.ext (h.gauge i U g))))
    · exact dolled k _ (h.real i U)
    change ‖token c N r (k • V'.mean i U)‖≤_; rw [map_smul,norm_smul]; exact mul_le_mul_of_nonneg_left (hp i U) (norm_nonneg k)
lemma zinc (k:ℝ)(U:Grid c) (i:I): letters (renS S k) p U i=k • letters S p U i:=by
    unfold letters; by_cases he:Healthy p (S.addr i).support U
    · rw [masked_eq _ (S.addr i).support _ U he]; exact masked_eq _ _ _ _ he -- renS rw lhs defeq? check
    · rw [masked_ne _ (S.addr i).support _ U he,smul_zero]; exact masked_ne _ _ _ _ he
variable {U: Grid c→EvenA c N}
lemma zoomL (h:Bound S X G V' B n Δ θ ρ r b t U)(hv:0≤b)(hk:1≤ r)(ht:0 ≤ t)(k:ℝ): Bound (renS S k) X (renS G k) (renV V' k) B n (‖k‖*Δ) (‖k‖*θ) (‖k‖*ρ) r b t (k • U) :=by
   refine ⟨breath _ _ h.tilled k,pokes _ _ h.rip k,scales _ h.loom k,topaz _ h.deed k,tranquil _ h.cash k,fun V=>?_⟩
   have hz: Patron.total (renS G k) B.threshold V=k • Patron.total G B.threshold V:= (( (permits _ h.loom (zero_lt_one.trans_le hk) hv V).hasSum.const_smul k).congr_fun (fun i=>zinc G k V i)).tsum_eq
   rw [hz,show (∑' i,(renV V' k).mean i V)= k • ∑' i,V'.mean i V from ((scaledLift V' h.cash V ht hk|>.hasSum.const_smul k).tsum_eq),Pi.smul_apply,h.earns,smul_add,smul_add,smul_sum]; simp_rw [zinc]
-- transport budgets
variable (S':Gem C N J) (X':Finset J) (L: Window c C D)(v:Site C→ℂ)
lemma framesQ (hp: LiftQ L S S' X X' v B w)(k:ℝ): LiftQ L (renS S k) (renS S' k) X X' v B n:=by
    have hp {I:Type}{n:Side}(S:Gem n N I)(x:Finset I)(z:Site n)(W:Grid n): orchid x (renS S k) z W=k • orchid x S z W ∧ duskQ x (renS S k) z W=k*duskQ x S z W:=by
       constructor; · unfold orchid primed; change buds z N (∑ i∈x,k • S.view i W)=_; rw [← Finset.smul_sum,map_smul]; rfl
       unfold duskQ; rw [Finset.mul_sum]; refine sum_congr rfl fun i hi=>?_ ; change river n N (k • S.view i W)/ _= _; rw [map_smul,smul_eq_mul,mul_div_assoc]; rfl
    constructor; intro i U hx; obtain ⟨h',hz⟩:= (show LiftQ L S S' X X' v B w from ‹_›).rays i U hx; rw [(hp ..).1,(hp ..).1,(hp ..).2,(hp ..).2,h',hz]; exact ⟨(map_smul (axes L v N).toLinearMap k _).symm,rfl⟩ -- shadows
end YM.QCD.Stem
