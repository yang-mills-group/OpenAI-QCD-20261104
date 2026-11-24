import YM.QCD.Fold.Quay
import YM.QCD.Smoke.Proof
import YM.QCD.Port.Mask
/-! # unfolding natural all-field rows -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Folding
open Function Lattice Wilson Lat Flume Orbit Run Fork Kit Cost Finset Relation
open PhysicalNext.Repeat.Deck Push.Local Further.PhysicalPeriodLimitF933 Macrame Shingle
open Bay Strut Sway Revolve Quarry Port RG Leaf Tee LeafM Rudder Eyrie Sparks Garden Pine YM.Next.Free
open scoped Classical Matrix Matrix.Norms.L2Operator BigOperators
variable {c C f F:Side}{D b B j k:ℕ}(X: Flight j k){e : f.val=c.val*X.L.val}{E:F.val=C.val*X.L.val}(h:C.val=c.val*D)(hl:2≤c.val)
variable (d:Site F→ℂ)(hd:Quaint (Lace.project (P:=X.patch) (h:=e) (H:=E) h hl).high d)
local notation "V"=> Lace.project (P:=X.patch) (h:=e) (H:=E) h hl
local notation "r"=>sliceL X e
local notation "R"=>sliceL X E
lemma balmW (T:Plan j)(K:Train j)(T':Window c C D)(y: Site C→ℂ)(hy:Quaint T' y)(U:Grid c): wood T 0 K (T'.links U)*stream T' y=stream T' y*wood T 0 K U:=by
   obtain ⟨t,p,hT,hCL,H⟩:=Rudder.pays_all T; obtain ⟨I,M,P,H⟩:= H K; have hg:= raw (P:=queen ∘ M) (trek P) U _ hy; have hh {n:Side} (A:Grid n): dust (queen ∘ M) n A=wood T 0 K A:=by unfold dust; simp_rw [Function.comp_apply, queen_rides]; exact (H ..).tsum_eq
   rw [hh,hh] at hg; exact hg
lemma dips (U:Grid f): lowC R ((V).high.links U)=(V).low.links (lowC r U):=by funext i; unfold lowC; rw [(V).high.traveller,show (V).high.cut ((R).embed i.1)=_ from (V).stake _]; rfl
variable {Q:Plan j}{P:Plan k}{t z a p A m q w u η p' z' A' Ω:ℝ}{n:ℕ} {Z : Offer 1 t p}{U':Offer 2 a A}{Ox:ℕ→Atom su 2}
lemma wildL (T:Offer n t p) (Y: Window f F D)(d) (hd:Quaint Y d)(hp:0<t)(hz:0<z)(hq:z ≤1)(U:Grid f): wild (frosting T.W) z F (Y.links U)*stream Y d=stream Y d*wild (frosting T.W) z f U:=by
   have hx := coined (t/(1+n)) (by positivity) T.price (by rw [div_mul_cancel₀ _ (by positivity)])
   have hk {m:Side}(U:Grid m):Summable fun i=>trackP (frosting T.W i) z _ U :=(LeafM.earns U hx hz hq (by positivity)).of_norm
   let P: Sheet F→L[ℂ] Rail F f:=LinearMap.toContinuousLinearMap {toFun:=fun M=>M*stream Y d,map_add':=fun _ _=>Matrix.add_mul ..,map_smul':=fun _ _=>Matrix.smul_mul ..}
   let Q: Sheet f→L[ℂ] Rail F f:=LinearMap.toContinuousLinearMap {toFun:=fun M=>stream Y d*M,map_add':=fun _ _=>Matrix.mul_add ..,map_smul':=fun _ _=>Matrix.mul_smul ..}
   change P _=Q (wild (frosting T.W) z f U); unfold wild; rw [P.map_tsum (hk (Y.links U)),Q.map_tsum (hk U)]; refine tsum_congr fun i=>?_ ; let b:= frosting T.W i; change yard b z (Y.links U) * routeM 0 (Y.links U) b.tail * stream Y d=stream Y d*(yard b z U*routeM 0 U b.tail); rw [Matrix.mul_assoc,ray_paths hd, ← Matrix.mul_assoc]; unfold yard; rw [peered Y d _ _ (Equiv.refl _) (fun x=> satin b x z U) (fun x=> rfl) (fun x=>?_),Matrix.mul_assoc] -- edit
   simp only [Equiv.refl_apply,satin,pulp,Slot.atSite,Y.expansion]
include hd
lemma taxedX (hT:0<t)(hA:0<a)(hz:0<z)(hq:z≤1)(U:Grid f): trunkM Z U' z m F ((V).high.links U)* stream (V).high d=stream (V).high d*trunkM Z U' z m f U:=by
   unfold trunkM blossomT; simp only [Pi.add_apply,Pi.smul_apply, Pi.one_apply,Matrix.mul_add,Matrix.add_mul,Matrix.smul_mul, Matrix.mul_smul,Matrix.one_mul, Matrix.mul_one]; rw [wildL Z _ _ hd hT hz hq U,wildL U' _ _ hd hA hz hq U]
lemma gatheredX (hT:0<t)(hA:0<a)(hz:0<z)(hq:z≤1)(U:Grid f): park X E Q Z U' z m ((V).high.links U)* stream (V).high d=stream (V).high d*park X e Q Z U' z m U:= mats_lift X Q V _ _ d hd U (taxedX X h hl d hd hT hA hz hq U)
-- note diagonal atoms per Signed & seam applies all
lemma paneW (Ox:ℕ → Atom su n)(U:Grid f)(s:Signed): AtomF.pane Ox (s,0) ((V).high.links U)*stream (V).high d=stream (V).high d * AtomF.pane Ox (s,0) U:=by
   let g:Strut F:=(s,0); let k: Strut f:=(s,0); have hx := pegs (V).high (divides (fineP (P:=X.patch) e E h)) rfl (show g.1=k.1 from rfl) (show (V).high.cut g.2=k.2 from map_zero (splitter _))
   have hp x:(V).high.cut ((act g).symm x)= (act k).symm ((V).high.cut x):=by
      apply (act k).injective; rw [show act k _ =_ from (show act k ((V).high.cut ((act g).symm x))=_ from Eq.symm (congr_fun hx.2 ((act g).symm x))),comp_apply,Equiv.apply_symm_apply,Equiv.apply_symm_apply]
   have hY: sky g ((V).high.links U)=(V).high.links (sky k U):=by
     funext i; unfold sky pull Window.links; change Lattice.Step.read _ ((V).high.links U) _ = Lattice.Step.read _ U _; rw [Window.read]; apply congr_arg; exact congr_fun hx.2 i.1
   have hh x: AtomF.per Ox g ((V).high.links U) x=AtomF.per Ox k U ((V).high.cut x):=by unfold AtomF.per; rw [hY]; unfold Atom.unmasked Slot.atSite; simp_rw [(V).high.expansion,hp]
   unfold AtomF.pane AtomF.field; apply peered (V).high d _ _ _ _ (fun x=> rfl); intro x; exact congr_arg (fun y:ℝ=>d x • ((y:ℂ) • (1:Bundle))) (hh x)
lemma probed (hv:Species X E w p' z' η A' b (park X E Q Z U' z m))(hp:Species X e w p' z' η A' b (park X e Q Z U' z m))(hT:0<t)(hA:0<a)(hz:0<z)(hq:z≤1)(U:Grid f)(Ox:ℕ→Atom su 2):
   probe w (park X E Q Z U' z m) Ox ((V).high.links U)* stream (V).high d = stream (V).high d* probe w (park X e Q Z U' z m) Ox U:=by
    unfold probe; simp only [Pi.sub_apply, Matrix.sub_mul,Matrix.mul_sub]; have he : (AtomF.robe Ox ((V).high.links U))*stream (V).high d=stream (V).high d*AtomF.robe Ox U:=by
        unfold AtomF.robe; rw [Matrix.mul_smul,Matrix.smul_mul]; simp only [Matrix.sum_mul,Matrix.mul_sum]; apply congr_arg; refine sum_congr rfl fun i _=>paneW X h hl d hd Ox U i
    rw [he]; apply congr_arg₂ (·-·) _ rfl; exact Smoke.log_stream (d:=w) (gatheredX X h hl d hd hT hA hz hq U) (hv.pupils _) (hp.pupils _)
lemma kiosk (hv:Species X E w p' z' η A' b (park X E Q Z U' z m))(hp:Species X e w p' z' η A' b (park X e Q Z U' z m))(hT:0<t)(hA:0<a)(hz:0<z)(hq:z≤1)(U:Grid f): dusk X E P (park X E Q Z U' z m) ((V).high.links U)*stream (V).low (d ∘ (R).embed)= stream (V).low (d ∘ (R).embed)* dusk X e P (park X e Q Z U' z m) U:=by
    simp only [dusk,Pi.sub_apply,Matrix.mul_sub,Matrix.sub_mul,comp_apply,dips X h hl, balmW P X.land (V).low (d ∘ (R).embed) (descend X V hd)]; apply congr_arg₂ (·-·) rfl; exact panels X Q V _ _ d hd U (hp.sole _) (hv.sole _) (taxedX X h hl d hd hT hA hz hq U) -- args
end YM.QCD.Folding
