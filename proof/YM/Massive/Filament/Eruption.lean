import YM.Massive.Commerce.Degrees
import YM.Massive.Filament.Loop
/-! # Arc stability through initial raw step (graph billing launch).

Don't require already-projected or oriented outputs here. They will be oriented
*after* the marker allocation. `honest` communicates analyticity to the `portion`
in `mission` at every label with K-address unchanged. This is before reanchoring and K-migration.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Loom.Fleet
open ConnectedActivityE6
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets Horticulture
open Mixed Reserves Trees Beam Cove Leaf Lat PhysicalNext.Repeat.Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical PhysicalNext.Repeat.Greenbelt
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{δ β τ μ W C:ℝ} {R:Rep su f}{F Z:Tree.Forest S.ratio}{Q:Target su P}{o :Target.Order su W}
variable {H:Cash W τ μ L Q o C T R}{ι:Type}{N:ℕ}
local notation "I'"=> Pipe.Clump S ι
variable (Y:Fleet H ι N)
open Art Blaze Polar Shield Frond GasP Ursell Graph Patron
variable (p:ℂ→ℂ→ι→Grid f→Grid c→EvenA c N)
set_option quotPrecheck false
-- given the same address, unmarked K/E commute owner.Structures with full tag-state
local notation "E'"=> fun z s:ℂ=> version Y (p z s)
variable (χ: Chi)
open Massive.Filament
variable (a:ι→ℂ→ℂ→ℂ)
variable (ha:∀ i,Fused (a i)) (hx:∀ i (z s:ℂ), ‖z‖<1→‖s‖<1→ ‖a i z s‖≤1)
variable (h: ∀ i U V z s, ‖z‖<1→‖s‖<1→p z s i U V=a i z s • Y.works i U V)
variable (hp:∀ V,Summable (fun i=> Y.honest χ V i))(hf:∀ z s:ℂ, ‖z‖<1→‖s‖<1→ (version Y (p z s)).Famous)
variable (V:Grid c)
include a ha h
lemma fused_slot (x:I') : Fused (fun z s:ℂ=> vF ((E') z s) x χ V):=by
    have hF:Fused (fun z s=> ∏ i∈ x.toRight,a i z s):= Fused.multiple _ _ fun i _=>ha i; refine (hF.compose (· • vF Y x χ V) (by fun_prop)).congr _ fun z s hz hs=> ?_; exact vF_scaled Y _ _ (fun i U V=> h i U V z s hz hs) ..
omit h in
lemma finray (x:Clusters Y.Bright) : Fused (fun z s=> marked_amount Y (fun i=> a i z s) x):=Fused.multiple (fun i z s=> ∏ j∈ (x.2 i).val.toRight,a j z s) Finset.univ fun _ _=> Fused.multiple _ _ fun j _=> ha j
lemma fused_honest (x:Clusters Y.Bright) : Fused (fun z s=> honest ((E') z s) χ V x):=by
    refine ((finray Y a ha x).compose (fun p:ℂ=> p • honest Y χ V x) (by fun_prop)).congr _ fun z s hz hs=> ?_; exact honest_scaled Y _ _ (fun i U V=> h i U V z s hz hs) .. -- infer arguments
include hx
omit ha in
lemma fdr (tp : Clusters Y.Bright) (z s:ℂ)(hz:‖z‖<1)(hs:‖s‖<1): ‖honest (version Y (p z s)) χ V tp‖ ≤ ‖honest Y χ V tp‖:=by
    calc
      _ = ‖marked_amount Y (fun i=>a i z s) tp‖*‖honest Y χ V tp‖:= Eq.trans (congr_arg (‖·‖) (honest_scaled Y (p z s) (fun i=>a i z s) (fun i U V=> h i U V z s hz hs) tp V)) (norm_smul ..)
      _ ≤ _:= by
         refine mul_le_of_le_one_left (norm_nonneg _) ?_; unfold marked_amount; simp_rw [norm_prod]
         exact prod_le_one (fun _ _=>prod_nonneg (fun _ _=>norm_nonneg _)) fun _ _=> prod_le_one (fun _ _=>norm_nonneg _) fun j _=> hx j z s hz hs

include hp hf
lemma arc_portion (u: Support c): Fused (fun z s=> portion Y.lightF (dawnV (version Y (p z s)) χ V) u):=by
    let J:= E'
    let M(x:Clusters Y.Bright)(z s:ℂ):= if unionOf Y.lightF x.2=u then honest (J z s) χ V x else 0
    let q(x:Clusters Y.Bright):= ‖honest Y χ V x‖; have hs: Summable q:= (hp V).norm -- via fd
    have hJ (x: Clusters Y.Bright): Fused (M x):=by
       by_cases hj : unionOf Y.lightF x.2=u
       · unfold M; simp_rw [if_pos hj]; exact fused_honest Y p χ a ha h V x
       unfold M; simp_rw [if_neg hj]; exact Fused.steady (0:EvenA c N)
    have hU (x: Clusters Y.Bright) (z s:ℂ)(hz:‖z‖<1)(hs:‖s‖<1): ‖M x z s‖≤ q x:=by
       unfold M q; split
       · exact fdr Y p χ a hx h V x z s hz hs
       exact norm_zero.trans_le (norm_nonneg _)
    refine (Fused.roll hJ hs hU).congr _ fun z s hz hs=> ?_; apply tsum_congr ;intro i; unfold M; split
    next hh=> exact ((J z s).phoenix χ V (hf z s hz hs) i).symm
    next hh=> rfl

lemma arc_motto (x:Y.Faber): Fused (fun z s=>motto Y.broad Y.invD Y.lightF (RG.flags (Pressure.temp τ) V) (duskV ((E') z s) χ V) (dawnV ((E') z s) χ V) x.val):=by
    let J:= (E'); unfold motto
    let X z s (i:Y.Dark ⊕ Support c):= samples Y.lightF (duskV (J z s) χ V) (dawnV (J z s) χ V) i
    change Fused (fun z s=> ite (wagon Y.broad x.val ∧ RG.flags (Pressure.temp τ) V ∩ wound Y.broad x.val=sweep Y.invD x.val) _ _)
    by_cases hn:wagon Y.broad x.val∧ RG.flags (Pressure.temp τ) V∩ wound Y.broad x.val=sweep Y.invD x.val
    swap; · simp_rw [if_neg hn]; exact Fused.steady (0:EvenA c N)
    simp_rw [if_pos hn]; apply Fused.multiple (fun i z s=> X z s i)
    intro i _; rcases i with i|u
    · exact fused_slot Y p χ a ha h V i.val
    change Fused (fun z s=> NormedSpace.exp (-(portion Y.lightF (dawnV (J z s) χ V) u))-1)
    exact (arc_portion Y p χ a ha hx h hp hf V u).minusC.exponential.minus (Fused.steady (1:EvenA c N))
lemma arc_mission (x:Y.Faber): Fused (fun z s=> mission ((E') z s) χ V x.val):= arc_motto Y p χ a ha hx h hp hf V x

def flexClaim (q:ι→Grid f→Grid c→EvenA c N): Rail c N Y.Faber:= ⟨(claim Y χ).addr, fun i V=> mission (version Y q) χ V i.val⟩
omit a ha hx h hp hf in
private lemma hats_equal (P Q:Hat c)(h:P.place=Q.place)(he:P.inv=Q.inv):P=Q:=by cases P; cases Q; congr
omit a ha hx h hp hf in
lemma fca_eq (q:ι→Grid f→Grid c→EvenA c N): (flexClaim Y χ q).addr=(claim (version Y q) χ).addr:= funext fun _=> hats_equal _ _ rfl rfl -- kernel
omit a ha hx h hp hf in
lemma fc_eq (q:ι→Grid f→Grid c→EvenA c N): (flexClaim Y χ q)=(claim (version Y q) χ):=by unfold flexClaim; have hh: (claim Y χ).addr=(claim (version Y q) χ).addr:=fca_eq Y χ q; rw [hh]; rfl
omit a ha hx h hp hf in
private lemma exactArc {ι:Type} (A: ι→ Hat c)(p: ℂ→ℂ→ι→Grid c→EvenA c N)(hp:∀ i U,Fused (fun z s=> p z s i U)): Fibre.Arc (fun z s=>(⟨A,p z s⟩:Rail c N ι)):=⟨fun _ _=>rfl,hp⟩
lemma arc_claim: Fibre.Arc (fun z s=> flexClaim Y χ (p z s)):=
    exactArc (claim Y χ).addr (fun z s i V=> mission (version Y (p z s)) χ V i.val) fun x U=> arc_mission Y p χ a ha hx h hp hf U x

end YM.QCD.Loom.Fleet
#print axioms YM.QCD.Loom.Fleet.fc_eq
#print axioms YM.QCD.Loom.Fleet.arc_claim
