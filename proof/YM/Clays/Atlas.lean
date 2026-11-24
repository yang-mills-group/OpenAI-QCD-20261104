import YM.Clays.Rates
import YM.Oars.Treads
import YM.MassiveQCD.Chariot.Reticule
import YM.MassiveQCD.Lyre.Gleam
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample
open QCD QCD.Grass QCD.Cove Lattice Finset Ribbon Cupola Stew
open Function Lattice Wilson Creek Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph QCD.GasP PhysicalNext.Repeat.Turn Patron Kites Ribbon Cupola Plate Plate.Card Relight Ruby Massive.PCAC
open scoped Topology BigOperators ContDiff Classical Matrix Matrix.Norms.L2Operator
namespace Basal
variable {c:Side}{N:ℕ}{I D:Type}[Fintype I]{a C t b w x v θ m:ℝ}
variable (o:I→Site c)(p:I→Lat.Fields c 6→L[ℂ]Lat.Fields c 6) (H:∀ i,Veins (o i) (p i) C) (s:List I)(d:I→ℂ)
local notation "P"=> Patio (Keys c 6⊕Spine I)
local notation "M"=> ample 6 I
local notation "T"=> traceI I
local notation "Λ"=> Keys c 6
local notation "K"=> actE o p H d s
local notation "Γ"=> effect o p H d
local notation "amt" j:arg=> (s.filter (fun i=> i∈ (j:Finset I)))
variable (F: Reel c 6 I D) {U:BudgetPoint}
local notation "B!"=> U.B
-- receipt at one root abstract allowance.all supports including new root enabled only inside. T.Mark exponent Ψ.
structure Script (F:Reel c 6 I D) where
    foot:D→Site c
structure ValidX (f:D→Site c)(g:D→ℝ)(U:BudgetPoint)(t:ℝ) : Prop where
    prepare i:f i ∈ (F.addr i).support
    start i:(F.z i).image o⊆ (F.addr i).support
    permit i: Measurable (F.mark i)
    room i: LocalOn (F.addr i).support (F.mark i)
    costume i U : Stitch.lights (F.z i) (F.addr i).support o (traceI I) (F.mark i U)
    tint i U g: parcelColor 6 g I (F.mark i (Lattice.gauge g U))= F.mark i U
    fee i: Sight (F.addr i).support (f i) 2 U t (Reel.speaker (traceI I) F i) (g i)
variable (f:D→Site c)(g:D→ℝ)(h:ValidX o F f g U t)
noncomputable def matings (i:D):Finset (Finset I):=(s.toFinset∩ barn o (F.addr i).support).powerset.filter fun j=> j.Nonempty∧Disjoint j (F.z i)
noncomputable abbrev Oper:=Sigma fun i:D=> ↥(matings o s F i)
noncomputable def clayR: Reel c 6 I (Oper o s F):=⟨F.addr ∘ Sigma.fst, fun i=> i.2.val∪F.z i.1, fun i V=> Γ (s.filter fun j=>j∈i.2.val) (F.mark i.1 V)⟩
local notation "E"=> Oper o s F
local notation "Ψ"=> clayR o p H s d F
include H h
lemma outline(i:D)(j:Finset I)(hz:j∈matings o s F i): j ⊆ s.toFinset ∧ j.Nonempty∧ j.image o⊆ (F.addr i).support∧ Disjoint j (F.z i):=by
     obtain ⟨hx,hr,hf⟩:=mem_filter.mp hz; have hh:=mem_powerset.mp hx; refine ⟨hh.trans inter_subset_left,hr,?_,hf⟩; intro k hk; obtain ⟨z,hz,rfl⟩:= mem_image.mp hk; exact (inside ..).mp (mem_inter.mp (hh hz)).2
lemma booklet: Reel.Book o T Ψ:=by
   have h₁(i:E):= outline o p H s F f g h i.fst i.snd.val i.snd.2 -- warns H unused
   refine ⟨fun i=>(h₁ i).2.1.mono subset_union_left,fun i=>?_,fun i=> (Γ (s.filter fun j=>j∈i.2.val)).measurable.comp (h.permit _),fun i U V hu=>congr_arg (Γ _) (h.room i.1 U V hu),fun i V=>?_,fun i V g=> (pay_spots o p H d _ _ _).symm.trans (congr_arg _ (h.tint i.1 V g))⟩ -- binder order
   · change (i.2.val∪F.z i.1).image _⊆_; rw [image_union]; exact union_subset (h₁ i).2.2.1 (h.start i.1)
   refine ⟨?_,pay_clan o p H d (s.filter fun j=> j∈i.2.val) _ _ (h.costume i.1 V).2⟩; change Polite T (i.snd.val∪ F.z i.fst) (effect o p H d _ _); have hf:= pay_piece o p H d (s.filter fun j=>j∈i.2.val) (h.costume i.1 V).1; rw [viewingP s _ (h₁ i).1] at hf; exact hf
-- local markup arrays retain original mask. valuation.Sight after re-anchor. Chart retrieval from scrape through Slice.Local. use finite-dimensional lift via `exists_left...` etc.`
omit H h
-- lemma retrieval represent actual Patio part as chosen left.Lmap.Computable from linear equiv. explicit plus stabilization. PLUS uses Polite.λ. Could use finite dim right ext.
noncomputable def portar (r:Finset I) : Lat.Fields c 6 →L[ℂ] P:=by
    let f:Lat.Fields c 6→L[ℂ]Alg (Λ⊕Spine I):=Ribbon.stake Λ (burst T r); let g:Alg (Λ⊕Spine I)→ₗ[ℂ]Alg (Λ⊕Spine I):= (2:ℂ)⁻¹ • ((LinearMap.id:Alg (Λ⊕Spine I)→ₗ[ℂ] Alg (Λ⊕Spine I))+grade.toLinearMap); let p:= g.comp f.toLinearMap; exact LinearMap.toContinuousLinearMap (p.codRestrict (roomA _).toSubmodule fun x=> (show Plus (p x) from (plus_grade _))) -- plus order inspect
lemma porterR (r:Finset I)(x:P)(h:Polite T r x): portar r (pluck Λ (burst T r) x)=x:=by
    apply Subtype.ext; change (2:ℂ)⁻¹ • (stake Λ _ _+Grass.grade (stake Λ _ _))= _; rw [show stake Λ _ (pluck Λ (burst T r) x)=_ from h.exact, (show Grass.grade x.val=x.val from (bright x))]; rw [← two_smul ℂ x.val]; exact inv_smul_smul₀ (by norm_num) _
include H h
open ConnectedActivityE6 Blaze King
variable (hr: ∀ i:I, ‖d i‖≤a)(ha:0≤a)(hC:0 ≤ C)(ht:0<t)(hs:s.Nodup)
include ha hr hC ht hs

-- Woven power.B volume.P handles. Price at all test positions. WA & L. reach_A Δ
noncomputable def taste (U:BudgetPoint)(Y:Support c):ℝ:= Plate.reFee (King.wag Y U.B) 2 U*(1+(King.wag Y U.B:ℝ))^2
noncomputable def extreme (U:BudgetPoint)(a C:ℝ)(i:Oper o s F):ℝ:= taste U (F.addr i.1).support * ((C*a)^i.2.val.card*g i.1)
local notation "ψ" i:arg=> extreme o s F g U a C i -- binder order
set_option maxHeartbeats 690000 in
lemma prize (i:E) (j:Site c) (ht':j∈(F.addr i.1).support): Sight (F.addr i.1).support j 2 U t (Reel.speaker T Ψ i) (ψ i):=by
     let o':= f i.1; let k:= King.wag (F.addr i.1).support U.B; let f:= (s.filter fun j=>j∈ i.2.val); let V:=F.mark i.1; let t':= F.z i.1; let F':= Reel.speaker T F i.1; let g':= Ψ; let Z':= (Ψ).mark i; let a':= (Ψ).z i; let p₀:= Γ f; let p₁:=pluck Λ (burst T a'); let p₂:=pluck Λ (burst T t'); let p₃:= portar (c:=c) t'; have hf:= h.fee i.fst; let r':=(F.addr i.1).support; have hw := reticule (d:=k) hf ht.le (Corona.extent r' U.B (h.prepare i.1) ht'); have hb := booklet o p H s d F _ _ h; have hv: V= (p₃.restrictScalars ℝ) ∘ F' :=funext fun x=> (porterR _ _ (h.costume i.1 x).1).symm; let W:= Reel.speaker T g' i; have hz:Z'= p₀∘ V:=rfl; have hh:W=p₁∘ Z':= rfl; have hc(x)(hx:Healthy U.threshold r' x) : Push.Local.Chart U.order V x:=by rw [hv]; exact (p₃.restrictScalars ℝ).contDiff.contDiffAt.comp 0 (hf.use x hx)
     have hU(x)(hx:Healthy U.threshold r' x) : Push.Local.Chart U.order Z' x:=by rw [hz]; exact (p₀.restrictScalars ℝ).contDiff.contDiffAt.comp 0 (hc x hx)
     refine ⟨fun V W hp=> congr_arg p₁ (hb.room i V W hp),fun V=> (hb.stage i V).2 _,fun x hx=>(p₁.restrictScalars ℝ).contDiff.contDiffAt.comp 0 (hU x hx),fun x hx l hl hL=>?_,p₁.measurable.comp (hb.permit _),?_⟩
     · let u:=leftDerivs V l x; let v:= leftDerivs F' l x; let Q:= leftDerivs W l x; have he': v=p₂ u:=Push.Local.left_linear (p₂.restrictScalars ℝ) l (hc x hx) hl; have hQ: Q=p₁ (p₀ u):= by unfold Q; change leftDerivs ((p₁.restrictScalars ℝ)∘Z') l x=_; rw [left_linear _ _ (hU x hx) hl,hz,show leftDerivs (p₀ ∘ V) l x=p₀ u from left_linear (p₀.restrictScalars ℝ) l (hc x hx) hl]; rfl
       have hhX: Polite T t' u:=by
           apply Polite.of_ranges; intro j hj; change pluck Λ j u=0; let z:=(pluck Λ j).restrictScalars ℝ
           unfold u; rw [←show leftDerivs (z∘V) l x=pluck Λ j _ from left_linear z l (hc x hx) hl]; rw [show z ∘ V=fun _=>0 from funext fun _=> (h.costume ..).1.spectral j hj]; simpa only [ite_self] using! Work.G07.left_const (0:Lat.Fields c 6) l x
       have hZ: Q∈ Creek.region (limits r') := Lyre.stays_left ((Creek.region (limits (F:=6) r')).toSubmodule.restrictScalars ℝ) W (fun v => (hb.stage i v).2 _) l x
       let Hc:= Stitch.Tablet.credits (N:=6) (c:=c) (I:=I) t; have hψ:Hc u=load (fun _=>t) v:=by rw [he']; exact Stitch.Tablet.polite_bill _ _ hhX ht
       have htL:i.2.val⊆s.toFinset:=(outline o p H s F _ _ h _ _ i.2.2).1; have hlL:f.length= i.2.val.card:=payScope s hs _ htL; have hhL:Polite T a' (p₀ u):=by have hΦ1:f.toFinset∪t'= a':=congr_arg (fun u=>u∪t') (viewingP s _ htL); rw [←hΦ1]; exact pay_piece o p H d f hhX
       have hZL:load (fun _=>t) Q≤ (C*a)^i.2.val.card *(Plate.reFee k 2 U * g i.1):=by
               have hQ':= price_all o p H d ht hr ha hC f u; change Hc (p₀ u)≤_*Hc u at hQ'; rw [hlL,hψ] at hQ'; exact ((le_of_eq (show load (fun _=>t) Q=Hc (p₀ u) by rw [hQ]; exact (Stitch.Tablet.polite_bill _ _ hhL ht).symm)).trans hQ').trans (mul_le_mul_of_nonneg_left ((Plate.viewer j v 2 ht).trans (hw.pole x hx l hl hL)) (pow_nonneg (mul_nonneg hC ha) _)) -- .. syntax
       exact (Plate.rangeView j Q 2 ht r' hZ ht' (B:=U.B)).trans ((mul_le_mul_of_nonneg_left hZL (by positivity)).trans_eq (by unfold extreme taste k r'; ring)) -- expensive unfold k
     unfold extreme taste; have ht:=hf.travels; unfold reFee; positivity
end Basal
end YM.MassiveQCD.Sample
#print axioms YM.MassiveQCD.Sample.Basal.prize
