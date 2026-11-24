import YM.Helio.Pouch
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
-- contour pos≤Lt.Wait
structure CreditBeam (Z:ℝ):Prop where
    ticket : 0 < Z
    bill (c:Side)(U:Grid c)(Y:Support c)(α:Axis)(t:ℝ):Healthy t Y U→0<t→ Spice.beamAt Y (overlayP α U) U (Z*t)
lemma solvent :∃ Z,CreditBeam Z:=by obtain ⟨Z,h,h'⟩:=overlayCost; exact ⟨Z,h,h'⟩
variable {Z:ℝ}
variable (hZ: CreditBeam Z)(hq:Run.Pack id id η δ B U q G A)(hv:Torch G)
include hq hv hZ
lemma usesP (V:Grid c)(hp:Healthy p.threshold R V) (hη:0<η)(ht: Z*p.threshold<η/2): ‖L V‖ ≤ silos A d*(Z*2)*(p.threshold/η):=by
    rw [penny V x d G hq hv]; let S:= (d.2.2:Support c); have hE:=p.threshold_pos; have hm:=hZ.bill c V R x p.threshold hp hE; apply (norm_mul_le ..).trans; apply (mul_le_of_le_one_right (norm_nonneg _) (rotation_price (show letterP V x d.2.1∈unitary _ from touch_u (thread_u ..)))).trans; exact (Spice.cruise (hq.crop d.1 d.2.1 d.2.2) (Spice.mores hm subset_union_left) hη ht (mul_nonneg hZ.ticket.le hE.le)).trans_eq (by unfold silos; ring)
omit hq hv hZ
open Push.Uniform WardBin.Lies Metric
lemma polarRep (i j:Site c)(S:Support c)(o:Site c)(h:o∈ S)(P:Pulse c→ Bundle)(ht: Crop i j η S P a) (hg:0<η)(hf:η ≤1)(hv:p.threshold ≤ η) (l:List (Directions su c))(V:Grid c)(hx: ∀ x∈l,p.dirBound o x) :
 let p':={p with threshold:=η,threshold_pos:=hg,threshold_le:=hf}; ∃ m:List (Directions su c),m.length=l.length ∧ (∀ i∈m,p'.dirBound o i)∧ leftDerivs (P ∘ settled) l V=(p.threshold/η)^l.length • leftDerivs (P∘settled) m V := by
    intro p'; let r:=p.threshold/η; have hE:=p.threshold_pos; have hr:0<r:=div_pos hE hg
    let k:=l.length; let Y:= l.get; let Q: Slab su c k := r⁻¹ • Y
    let m:= List.ofFn Q; refine ⟨m,(List.length_ofFn),?_ ,?_⟩
    · intro i hi; obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hi; intro e; rw [show Q j e=r⁻¹ • Y j e from rfl,norm_smul,Real.norm_of_nonneg (inv_pos.mpr hr).le,inv_mul_eq_div]; refine (div_le_iff₀ hr).mpr ?_; apply (hx _ (l.get_mem j) _).trans; apply le_of_eq; unfold p' r; field_simp
    have he:= congr_arg ((P ∘ settled) ∘ journey V k Q) (rfl: (0:Panels k)=0)
    let M:= WardBin.Lies.mixed (P∘settled) k V
    change _= r^k • _; apply Eq.trans (show leftDerivs (P∘settled) l V=M Y from (by rw [← List.ofFn_get l, Germ.takes (milady ht hg V k) Y le_rfl]))
    have hm: ContinuousMultilinearMap ℝ (fun _ : Fin k=> Directions su c) Bundle:=M
    rw [show leftDerivs _ m V = M Q from Germ.takes (milady ht hg V k) Q le_rfl,show Y=(fun i=> r • Q i) from funext fun i=> (smul_inv_smul₀ hr.ne' _).symm, ContinuousMultilinearMap.map_smul_univ]; simp
-- get charges on difference
local notation "χ" i:arg=> weighT i A x

lemma polarBudget (n b B:ℕ): ∃ C:ℝ,0 ≤ C ∧∀ (c:Side)(S:Support c)(p:BudgetPoint)(P:Pulse c→Bundle)(o:Site c)(η a:ℝ)(i j:Site c), Crop i j η S P a→ o∈S→p.power≤b→p.order≤n→p.threshold ≤η→η≤1→∀ l:List (Directions su c),l ≠[]→l.length ≤p.order→(∀ i∈l,p.dirBound o i) →∀ V:Grid c, ‖leftDerivs (P∘settled) l V‖ ≤ (1+(diameterQ B S:ℝ))^(b*n)*(C*a)*(p.threshold/η):=by
    obtain ⟨C,hc,H⟩:=Entr.drops B n b; refine ⟨C,hc,fun c S p P o η a i j hp h hn hm hv hz l he hL hP V=>?_⟩
    let r:= p.threshold/η; have hη:= p.threshold_pos.trans_le hv; let p':={p with threshold:=η,threshold_pos:=hη,threshold_le:=hz}
    obtain ⟨m,hx,hQ,hk⟩:= polarRep i j S o h P hp hη hz hv l V hP -- unused hZ!
    have hs:0<r:=div_pos p.threshold_pos hη; have ht : r≤1:=(div_le_one hη).mpr hv; rw [hk,norm_smul, norm_pow,Real.norm_of_nonneg hs.le]; exact (mul_le_mul ((pow_le_pow_of_le_one hs.le ht (show 1≤l.length from List.length_pos_iff.mpr he)).trans_eq (pow_one r)) (H c p' P η a i j o S h hn hm le_rfl hp m (hx.trans_le hL) hQ V) (norm_nonneg _) hs.le).trans_eq (mul_comm ..)
end Meridian
end YM.QCD.Entr
#print axioms YM.QCD.Entr.Meridian.polarBudget
