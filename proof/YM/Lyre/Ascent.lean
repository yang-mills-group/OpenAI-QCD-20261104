import YM.Lyre.Range
import YM.Lyre.Canyon
import YM.TIPS.Cogs
/-! Combining MARKED forecasts on exact same mass RG kernels:
     - singular & mixed combo EP at level i
     - signed expansion accounts true bootstrap amidst bare operator tests.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Lyre
open Function Filter Lattice Wilson MeasureTheory QCD QCD.Lat QCD.Tide QCD.Grass
open Transfer QCD.Cove
open scoped Topology BigOperators Matrix.Norms.L2Operator Classical ComplexOrder
variable {S:Scheme}{R:Side}{N F i j:ℕ}(A:Run S N R F)
local notation "gR"=> S.side R
local notation "Pv" k=> S.step k
open MassiveQCD MassiveQCD.Sample MassiveQCD.Sample.Quills MassiveQCD.Sample.Quills.Eden Ribbon Cupola Plum Finset NormedSpace
section word
variable {I T:Type}[Fintype I][Fintype T]{k:ℕ}{c:Side}
noncomputable def emitK (q:I→Bool)(i:I) (x:Alg T) (h: Hom (q i) x): Patio (T⊕Spine I):= ⟨stake T (burst q {i}) x, even_stake (burst q {i}) x (Ribbon.flavor q i|>.symm ▸ h)⟩ -- missing Cove namespace
lemma overlap (q:I→Bool)(s:Fin k→I)(Ψ Y:I→ Alg T)(hp:∀ j,Hom (q j) (Ψ j))(he:∀ j,Hom (q j) (Y j))(hs:Injective s) :
   (List.ofFn (fun i=>Ψ (s i)+Y (s i))).prod=∑ p ∈(crest s).powerset, spliceG q s p • ((List.ofFn (fun i=> Ψ (tour p i))).prod * (List.ofFn (fun i=>Y (tour (crest s\p) i))).prod):=by
    let P(i:I):=emitK q i (Ψ i) (hp i); let L(i:I):=emitK q i (Y i) (he i); let G:= exp (∑ i:I,L i)
    have hL : ValidPieces T q univ G:= ValidPieces.exponent (ValidPieces.cost (A:=T) (q:=q) (U:=univ) univ L (fun i _=> ValidPieces.role {i} (show Polite q {i} (L i) from ⟨Y i,rfl⟩) (subset_univ _)))
    have h₁(p:Finset I): numbered q T (tour p) G=(List.ofFn (fun i=>Y (tour p i))).prod:=by
         have hx:= needleE T q (tour p) L Y (1:Patio T) (fun i=>rfl) (snug p); rw [map_one,one_mul,show (1:Patio T).val=1 from rfl,one_mul] at hx; exact hx
    have ht(i:I): (P i+L i).val=stake T (burst q {i}) ((Ψ+Y) i):= Eq.symm (map_add (stake T (burst q {i})) ..)
    have he0:= needleE T q s (fun i=> P i+L i) (Ψ+Y) (1: Patio T) ht hs; rw [map_one,one_mul,sum_add_distrib, exp_add,show (1:Patio T).val=1 from rfl,one_mul] at he0
    exact he0.symm.trans ((serveV T q s P Ψ G (fun i=>rfl) hL).trans (sum_congr rfl fun j _=>by rw [h₁]))
lemma songX (c:Side)(X:I→Stud c F) (s:Fin k→I)(V:Grid c): (List.ofFn (fun i=> X (s i) V)).prod=(List.ofFn (fun i=>X (s i))).prod V:=by
     induction k with|zero=> rfl|succ k ih=> rw[List.ofFn_succ,List.prod_cons,List.ofFn_succ,List.prod_cons, show (List.ofFn (fun i:Fin k=>X (s i.succ) V)).prod=_ from ih (Fin.tail s)]; rfl
lemma flockZ (X:I→Stud c F) (s:Fin k→I)(hx:∀ i∈ crest s, Stays (X i)): Stays (List.ofFn (fun i=>X (s i))).prod:=by
    induction k with
    | zero=> exact stays continuous_const
    | succ k ih=> have h(a:Fin (k+1)): Stays (X (s a)):=hx _ ((exists_fix ..).2 ⟨a,rfl⟩); rw[List.ofFn_succ,List.prod_cons]; exact (h 0).mult (ih (Fin.tail s) (fun i hi=>by obtain ⟨j,rfl⟩:=(exists_fix ..).1 hi; exact h j.succ))
-- functional Stays
lemma stockC (x:Stud c F)(u:ℂ)(hx: Stays x): Stays (u • x):=hx.flows (continuous_id.const_smul u)
lemma stampB(x:Stud c F)(u:ℂ) : joint (u • x)=u*joint x:=by unfold joint; simp only [Pi.smul_apply,map_smul,smul_eq_mul, integral_const_mul]
lemma stampM (q: Finset I)(x:I→Stud c F)(hx:∀ i∈ q, Stays (x i)):joint (∑ i∈q,x i)=∑ i∈q,joint (x i):=by
     unfold joint; simp only [Finset.sum_apply,map_sum]; rw[integral_finsetSum]; intro i hi; exact ((hx i hi).flows (ber (Modes c F)).continuous_of_finiteDimensional).intg _
end word
variable (A':Run S N R 6)
open QCD.Acre.Stratum.MarchQ.Suburb.Melt.Lobby
variable {I:Type}[Fintype I]{k :ℕ}(q:I→Bool)(s:Fin k→I)
-- old layers already carried via Y.Av; avg encoded externally here
variable (Γ0: Tones (S.side R i) I)(X: Insertion (S.side R N) 6)(Y:I→ Insertion (S.side R N) 6)(Ψ:I→Stud (S.side R i) 6)(L:I→ ∀ k,Set (Site (S.side R k)))
variable (hs:Injective s)(H:i≤N)(hv:∀ k:ℕ, i ≤ k→ k < N → ∀ a∈crest s,∀ b∈ crest s,a≠ b→ Disjoint (L a k) (L b k))(hΧ:∀ a∈ crest s, Lease i N (L a))(hX:∀ a:I,Plum.Fence (L a i) (Ψ a))(hx:∀ k:ℕ,i≤k→ k<N→ A'.w k≠0)(hP:∀ i:I,∀ V: Grid _,Grass.Hom (q i) ((Ψ i) V))(hQ:∀ i:I,∀ V: Grid _,Grass.Hom (q i) (Y i V))
variable (hT:∀ p⊆crest s, Γ0 p.card (Quills.tour p)=⇑(S.toStop R A'.β A'.w N i ((List.ofFn fun a=>Y (Quills.tour p a)).prod * X)))
include hs H hv hΧ hX hx hP hQ hT
lemma nucleate : joint (nurture (S.side R i) q Ψ Γ0 k s)=S.multiplier R A'.w i N 6 * joint ((List.ofFn fun j=> climbH A' i N (Ψ (s j))+ ⇑(Y (s j))).prod * ⇑X):=by
    let Zm:=(crest s).powerset; let M:=S.multiplier R A'.w i N 6
    let v(p: Finset I):=crest s \p; let K:=spliceG q s; let p':I→ Stud (gR N) 6 := fun a=> climbH A' i N (Ψ a);
    let G(p:Finset I):= (List.ofFn (fun i=>Y (tour (v p) i))).prod*X; let U(p: Finset I):=(List.ofFn (fun i=> Ψ (tour p i))).prod; let D(p:Finset I):=⇑(S.toStop R A'.β A'.w N i (G p)); let Z(p:Finset I):= (List.ofFn fun i=> p' (tour p i)).prod; have hU(p: Finset I):Stays (U p):=flockZ Ψ _ (fun i _=>(hX i).hp)
    have hz(p:Finset I):Stays (Z p):= flockZ p' _ (fun i _=> climbs A' (Ψ i) (hX i).hp H)
    have hX':nurture (gR i) q Ψ Γ0 k s=∑ p ∈ Zm, K p • (U p* D p):=by
         funext V; unfold nurture; rw [Finset.sum_apply]; refine sum_congr rfl fun p hp=> ?_; rw [songX,show Γ0 _ (tour (crest s \p))=_ from hT (crest s\p) sdiff_subset]; rfl
    have hc: (List.ofFn fun j=> p' (s j) + ⇑(Y (s j))).prod * ⇑X= ∑ p∈ Zm,K p • (Z p * (fun i=> G p i)):=by
         funext V; simp_rw [Finset.sum_apply]; rw [Pi.mul_apply, ← songX (gR N) (fun a=> p' a+⇑(Y a))]; change (List.ofFn (fun i=>p' (s i) V + Y (s i) V)).prod * _ = _; rw [overlap q s (fun i=>p' i V) (fun i=> Y i V) _ (fun i=>hQ i V) hs, sum_mul]; apply sum_congr rfl; intro p hp; rw [smul_mul_assoc, mul_assoc] ; rw [Pi.smul_apply, Pi.mul_apply]
         let f:= tour (v p); have hv:G p V=(List.ofFn fun i=>Y (f i) V).prod * X V:=by
             have h(L: List I):(L.map Y).prod V=(L.map (fun i=>Y i V)).prod:=by induction L with|nil=>rfl|cons a l ih=>rw[List.map_cons,List.prod_cons,List.map_cons,List.prod_cons,ContinuousMap.mul_apply,ih]
             have ht:= h (List.ofFn f); rw [List.map_ofFn,List.map_ofFn] at ht; exact congr_arg (fun a=>a*X V) ht
         rw [hv,show Z p V=_ from (songX _ p' (tour p) V).symm]
         intro i; exact steep A' _ _ (hX i).hp (hP i) H V
    have hj(p) (h:p∈ Zm): climbH A' i N (U p) = Z p:=by
         let f:= Quills.tour p; let l:=List.ofFn f; have he(a)(ha:a∈l):a∈crest s:=mem_powerset.mp h (by obtain ⟨j,rfl⟩:= List.mem_ofFn.mp ha; have H:f j∈crest f:= (exists_fix ..).2 ⟨j,rfl⟩; rwa[show crest f=p from club p] at H)
         have hv:= pieces A' l L Ψ (fun i _=>hX i) (fun i hi=> hΧ _ (he i hi)) (List.nodup_ofFn_ofInjective (snug p)) (fun k hk hj a ha b hb ht=> hv _ hk hj a (he a ha) b (he b hb) ht) H; unfold l at hv; rw[List.map_ofFn,List.map_ofFn] at hv; exact hv
    rw [hX',stampM _ _ (fun p _=> stockC _ _ ((hU p).mult (stays (ContinuousMap.continuous _)))),show joint _= _ from congr_arg joint hc,stampM _ _ (fun p _=> stockC _ _ ((hz p).mult (stays (G p).continuous))),Finset.mul_sum]; refine sum_congr rfl fun p hp=>?_ ; rw [stampB,stampB, show joint (U p*D p)=_ from soarL _ _ (hU p) H (G p) hx, hj p hp]; change K p*(M*_) = M*(K p* _); ring -- cast pi cout
end YM.Massive.Lyre
#print axioms YM.Massive.Lyre.nucleate
