import YM.Pollen.Bills
import YM.Clays.Benny
import YM.Clays.Acer
import YM.Bister.Body
import YM.Pollen.Oak
import YM.Helio.Ribbons
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample.Basal
open QCD QCD.Grass QCD.Cove Lattice Finset Ribbon Cupola Stew
open Function Lattice Wilson Creek Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph QCD.GasP PhysicalNext.Repeat.Turn Patron Kites Ribbon Cupola Plate Plate.Card Relight Ruby Massive.PCAC
open scoped Topology BigOperators ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{k:ℕ}{I D:Type}[Fintype I]{a t b w x v θ m:ℝ}
variable (o:I→Site c) {U:BudgetPoint}
variable (V: I→Grid c→ Fields c 6→L[ℂ]Fields c 6) (H:∀ i,Suit (o i) U a (V i)) (d:I→ℂ) (s:List I)
local notation "P"=> Patio (Keys c 6⊕Spine I)
local notation "S"=>Support c
local notation "q"=> traceI I
set_option quotPrecheck false
local notation "Φ" X:arg=> effU (fun k=> V k X) (fun k=> (H k).bean X) d
local notation "Ω" X:arg=> actU (fun k=> V k X) (fun k=> (H k).bean X) d
local notation "Z"=>Keys c 6
open ConnectedActivityE6 Blaze King
local notation "K"=> wag
local notation "T"=>Stitch.Tablet.credits
lemma coinStep (s: Finset I)(x:Grid c→P){V:Grid c}(ht:∀ i,Polite q s (x i))(hc: Chart U.order x V)(l:List (Directions su c))(h:l.length ≤ U.order) (hy:0 < t): T t (leftDerivs x l V)=load (fun _=>t) (leftDerivs (pluck Z (burst q s) ∘ x) l V):=by
     let u:=leftDerivs x l V; let z:=pluck Z (burst q s); have hhX: Polite q s u:=by
           apply Polite.of_ranges; intro j hj; change pluck Z j u=0; let z:=(pluck Z j).restrictScalars ℝ
           unfold u; rw [←show leftDerivs (z∘x) l V=pluck Z j _ from left_linear z l hc h]; rw [show z ∘ x=fun _=>0 from funext fun _=> (ht _).spectral j hj]; simpa only [ite_self] using! Work.G07.left_const (0:Lat.Fields c 6) l V
     rw [show leftDerivs (z∘ x) l V=z u from left_linear (z.restrictScalars ℝ) l hc h] -- need change view
     exact Stitch.Tablet.polite_bill _ _ hhX hy
variable (F:Reel c 6 I D)(f:D→Site c)(g:D→ℝ)(h:ValidX o F f g U t)
-- occ.
local notation "E"=> Oper o s F
local notation "Y" i:arg=> (F.addr i).support
local notation "gΦ" i:arg=> s.filter (fun j=>j∈ (i:Finset I))
noncomputable def etherU : Reel c 6 I (E):= ⟨fun i=> ⟨(F.addr i.1).site,growsZ o (Y i.1) i.2.val, mem_union_left _ (F.addr _).anchor⟩,fun i=>i.snd.val ∪ F.z i.1,fun i X=>(Φ X) (gΦ i.snd.val) (F.mark i.1 X)⟩
local notation "W"=>etherU o V H d s F
lemma memo (i:E): i.2.val ⊆ s.toFinset ∧ i.2.val⊆ barn o (Y i.1)∧ i.2.val.Nonempty∧ Disjoint i.2.val (F.z i.fst):=by obtain ⟨hx,h,h'⟩:=mem_filter.mp i.2.2; have hh:=mem_powerset.mp hx; exact ⟨hh.trans inter_subset_left,hh.trans inter_subset_right,h,h'⟩
include H h
lemma awardedU : (W).Book o q:=by
   refine ⟨fun i=>(memo o s F i).2.2.1.mono subset_union_left,fun i=> ?_,fun i=>measurableU o V H d (gΦ i.snd.val) (h.permit _),fun i X Y' hh=> ?_,fun i X=> ?_,fun i X g=> ?_⟩
   · intro i' hi; change i' ∈growsZ o (Y i.1) i.2.val; obtain ⟨j,hj,rfl⟩:=mem_image.mp hi; apply mem_union_left; rcases mem_union.mp hj with hj|hj; exact (inside ..).1 ((memo ..).2.1 hj); exact h.start i.1 (mem_image_of_mem _ hj)
   · let l:=gΦ i.snd.val; let A:= growsZ o (Y i.1) i.2.val; have hX: Agrees (growsZ o (Y i.1) l.toFinset) X Y':=by rw [show l.toFinset=i.2.val from viewingP s i.snd.val (memo o s F i).1]; exact hh
     exact congr_arg₂ (fun (z:P→L[ℂ]P) y=>z y) (readsU o V H d _ X Y' _ hX) (h.room i.1 X Y' (agrees_mono hh (show (Y i.fst) ⊆ A from subset_union_left)))
   · have he:=cladU o V H d (gΦ i.snd.val) X _ _ (h.costume i.1 X).2; have hp: Polite q ((gΦ i.snd.val).toFinset ∪ F.z i.1) ((W).mark i X):=pay_pieceU _ _ d (gΦ i.snd.val) (h.costume i.1 X).1; rw [viewingP s i.snd.val (memo o s F i).1] at he hp; exact ⟨hp,he⟩
   exact (colorU o V H d _ X g (F.mark i.1 (gauge g X))).trans (congr_arg _ (h.tint ..))
omit H
include h
lemma firstStep (i:D)(p:Grid c)(hz:Healthy U.threshold (Y i) p)(ht:0<t) : Phy t (F.mark i) p (U.dirBound (f i)) U.order (g i) 1:=by
    let f1:= Reel.speaker q F i; let x:=F.mark i; let s:= F.z i; have hx : x= (portar (c:=c) s) ∘ f1:=funext fun j=>(porterR _ _ (h.costume i j).1).symm; have hh: Chart U.order x p:=by rw [hx]; exact ((portar (c:=c) s).restrictScalars ℝ).contDiff.contDiffAt.comp 0 ((h.fee i).use _ hz)
    refine ⟨hh,fun l hv he=>?_⟩; rw [coinStep s _ (fun t=>(h.costume _ t).1) hh l hv ht,one_pow,mul_one]; exact (viewer _ _ _ ht).trans ((h.fee i).pole _ hz l hv he)
include H
variable (hs:s.Nodup)(hc:0 ≤a) (hx:0 ≤ x)(hp:0<t)(hd:∀ i,‖d i‖ ≤x)
local notation "A"=> (a*x)
noncomputable def mintA (i:E)(x:ℝ):= (a*x*(2:ℝ)^U.order)^i.snd.val.card*(g i.1) -- `a` hidden.A ? order U from return def. signature
local notation "m'" i:arg=> mintA (a:=a) (U:=U) o s F g i x
local notation "V!" i:arg=> ((W).addr i).support
noncomputable def mE (i:E)(x:ℝ):ℝ:= (1+(wag ((etherU o V H d s F).addr i).support U.B:ℝ))^(4+2*(U.power*U.order))*(mintA (a:=a) (U:=U) o s F g i x)
local notation "φ'" i:arg=>mE o V H d s F g i x
include hs hc hx hp hd
set_option maxHeartbeats 900000 in
lemma billsA (i:E)(j:Site c)(hk:j∈ V! i): Sight (V! i) j 2 U t (Reel.speaker q W i) (φ' i):=by
    let p:= f i.fst; let r:=F.mark i.1; let L:= Y i.1; let D:= V! i; let x':= (W).mark i; let u:=(W).z i; let f':= (pluck Z (burst q u)) ∘ x'; let k:=wag D U.B; let w:=1+(k:ℝ); have hw:1≤ w:= le_add_of_nonneg_right (Nat.cast_nonneg _); have hw0:=zero_le_one.trans hw; have he:D=growsZ o L i.2.val:=rfl; have hz:L⊆ D:=subset_union_left; have hP:p∈D:= hz (h.prepare _); have hb:(W).Book o q:=awardedU o V H d s F f g h; let q':= gΦ i.2.val; have hg ℓ (hl:ℓ∈ q'):separation (o ℓ) p ≤ k:=by
        have h0 := List.mem_toFinset.mpr hl; rw [show q'.toFinset=i.2.val from viewingP s _ (memo ..).1] at h0; exact Corona.extent _ _ (hz ((inside ..).1 ((memo ..).2.1 h0))) hP
    have hm: q'.length=i.2.val.card:=payScope s hs _ (memo ..).1; let x0:= A^q'.length*g i.1; let z:=1+(q'.length:ℝ)*w^U.power; have hZ :1 ≤ z:=le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hw0 _))
    have hX(X:Grid c)(hx':Healthy U.threshold D X): Phy t x' X (U.dirBound p) U.order x0 z:=phyU o V H d _ X hp p (firstStep o F f g h i.1 X (hx'.mono_left hz) hp) k hg hc hx hd
    let P':= 2+U.power*U.order; have hm0:0≤x0:=mul_nonneg (pow_nonneg (mul_nonneg hc hx) _) (h.fee _|>.travels)
    have hz':z ≤ 2^q'.length * w^U.power:=by
         have h:∀ n:ℕ,1+(n:ℝ) ≤ (2:ℝ)^n:=by
              intro n; induction n with| zero=>simp| succ n ih=> push_cast; rw [pow_succ]; linarith [Nat.cast_nonneg (α:=ℝ) n]
         apply le_trans (show z≤ w^U.power+(q'.length:ℝ)*w^U.power from add_le_add_left (one_le_pow₀ hw) _); rw [show w^U.power+(q'.length:ℝ)*w^U.power=(1+(q'.length:ℝ))*w^U.power from by ring]; exact mul_le_mul_of_nonneg_right (h _) (pow_nonneg hw0 _)
    let T':= w^P'*(m' i); have ht':0 ≤ T':=by unfold T' mintA; apply mul_nonneg (pow_nonneg hw0 _) (mul_nonneg (pow_nonneg (by positivity) _) (h.fee _|>.travels))
    have hs0 :Sight D p 2 U t f' T':=by
          let F0:= (pluck Z (burst q u)).restrictScalars ℝ; refine ⟨fun U V hu=> congr_arg F0 (hb.room i U V hu),fun V'=> (hb.stage i V').2 _,fun X h=> F0.contDiff.contDiffAt.comp _ (hX _ h).smooth,fun X hv l hl hL=>?_, F0.measurable.comp (hb.permit _),ht'⟩
          have hh:=hX X hv; let g':= leftDerivs f' l X; let Q:=T t (leftDerivs x' l X); have hQ: load (fun _=>t) g'=Q:=(coinStep ((W).z i) x' (fun x=>(hb.stage i _).1) hh.smooth l hl hp).symm; have hg:g'∈ Creek.region (limits D):= Lyre.stays_left ((Creek.region (limits (F:=6) D)).toSubmodule.restrictScalars ℝ) f' (fun v => (hb.stage i v).2 _) l X
          exact (rangeView p _ 2 hp D hg hP (B:=U.B)).trans ((mul_le_mul_of_nonneg_left (hQ.trans_le ((hh.paid l hl hL).trans (mul_le_mul_of_nonneg_left ((pow_le_pow_right₀ hZ hl).trans (pow_le_pow_left₀ (zero_le_one.trans hZ) hz' _)) hm0))) (sq_nonneg _)).trans_eq (by change w^2 * (x0*((2:ℝ)^q'.length*w^U.power)^U.order)=T'; unfold T' P' x0 mintA; rw[hm]; ring )) -- ring may fail variable exponents
    rw [show (φ' i) = Plate.reFee k 2 U*T' from ?_]; exact reticule hs0 hp.le (Corona.extent _ _ hP hk)
    unfold mE T' reFee; change w^(4+2*(U.power*U.order))*(m' i) =w^P' * (w^P'*(m' i)); rw [←mul_assoc (w^P'),←pow_add]; congr 2; unfold P'; omega
end YM.MassiveQCD.Sample.Basal
#print axioms YM.MassiveQCD.Sample.Basal.billsA
