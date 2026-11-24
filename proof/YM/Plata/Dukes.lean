import YM.Plata.Spice
/-!
Use independent walks, choose subseq stabilizing transport displacements. Note we do not consume the harmony cofinal limit once; all alphabet exposure is replayable. -/
set_option autoImplicit false
noncomputable section
namespace YM.Plata
open Function Set Filter Metric Lattice Wilson Massive Massive.Lyre Massive.Romance Goblet
open QCD QCD.Lat QCD.Tide QCD.RP QCD.Plum Chess Cells
open Patria Patria.Depth Patria.Hub Patria.Exposure
open UV Needle
open YM.Fir Massive.Fir NoteF Tarn Choir
open Bridge (reflect Cluster carry)
open scoped Topology BigOperators Classical ComplexOrder
variable {Q:Choir}{C:Sequence}{P:Calibration C}{φ:ℕ→ℕ}(hQ:Q.Harmony P φ)
variable {β ε:ℝ} (h:C.Path β ε)(hP:P.System)(hφ:Tendsto φ atTop atTop)
variable {I:Type*}[Fintype I]{m k n:ℕ} {u:ℝ} (z:I→ℂ) (w:I→List Bond)
variable {σ:ℝ}
set_option quotPrecheck false
local notation "Sz" i:arg=> C.S.side (C.R i) (C.N i)
local notation "R" i:arg=> (C.A i).regulator
local notation "α" i:arg=> C.S.spacing (C.N i)
def Quorum(n m:ℕ):= Fintype.card (Fin n × Fin m)* Fintype.card (Fin m)+1
noncomputable abbrev notch (q:E4)(d:ℕ)(σ:ℝ)(a:Axis):E4:= q+(d:ℝ) • ((2*σ) • basis a)
noncomputable abbrev pilfer (P:Calibration C)(w:I→List Bond)(s:Fin n→ Bool)(x:ℕ→ Cover)(Y:Fin n→ ℕ→ Cover)(a:Axis)(p:E4)(q:Fin n→E4)(f:Fin n→I): List Bond:= (List.ofFn fun i=> Borne P (s i) a x (Y i) p (q i) (w (f i))).flatten
omit [Fintype I] in
lemma waltz (s:Fin n→Bool)(a:Axis)(p:E4)(q:Fin n→E4)(x:ℕ→ Cover)(Y:Fin n→ ℕ→ Cover)(f:Fin n→I)(i:ℕ): wade (pilfer P w s x Y a p q f) i=Xq (P:=P) a (fun j=> wade (w j) i) s (x i) (fun j=> Y j i) f:=by
       unfold pilfer Xq wade; rw[List.map_flatten,List.map_ofFn]; congr 2; funext j; exact curls (w (f j)) x (Y j) p (q j) a (s j) i
variable (s:Fin n→Bool)(a:Axis)(D:Fin n→ℕ)
include h hP hφ
-- inputs **vary** during ledger proofs. freeze each march parity as whole only.
lemma pours (hp: Available P φ w z u σ m):∃ (F:Fin n→Fin (Quorum n m))(p:E4), ‖p‖≤3*σ ∧ ∃ (f:ℕ→ℕ)(b:ℕ→ Cover)(Y:Fin n→ℕ→ Cover), StrictMono f ∧ Loc C (φ∘f) b p ∧ (∀ i, Loc C (φ∘f) (Y i) (notch p (D i+(F i).val) σ a)) ∧ ∀ᶠ i in atTop, ‖(R (φ (f i))).average (cash P (φ (f i)) (Xq (P:=P) a (fun j=>wade (w j) (f i)) s (b i) (fun l=> Y l i)) (wealth s z))‖ ≤ u ^ n:=by
       let O:=Fin n→Fin (Quorum n m); haveI:Nonempty O:=⟨fun _=> ⟨0,Nat.zero_lt_succ _⟩⟩; let Θ (i:ℕ)(F:O)(t:Cover)(y:Fin n→ Cover):Prop:= ‖digit (α (φ i)) t‖≤3*σ ∧ (∀ j,digit (α (φ i)) (y j)= notch (digit (α (φ i)) t) (D j+(F j).val) σ a) ∧ ‖(R (φ i)).average (cash P (φ i) (Xq (P:=P) a (fun j=> wade (w j) i) s t y) (wealth s z))‖ ≤ u^n
       have he:Tendsto (fun i=> ((C.R (φ i)).val:ℝ)) atTop atTop:=tendsto_natCast_atTop_atTop.comp (h.infinite.comp hφ);
       have ht':∀ᶠ i in atTop,∃ F t y,Θ i F t y:=by
           let e (p: Bond) := hP.mixing p.d; filter_upwards [hp,he.eventually_ge_atTop ((2*(Fintype.card (Fin n × Fin m)*Fintype.card (Fin m)+1):ℝ)*σ), eventually_all.mpr (fun j:I=> (eventually_all_finset (w j).toFinset).mpr (fun p hp=> hφ.eventually (e p)))] with i hi hp hs
           apply stoppers h hP u z σ a _ s D hi hp; intro k x hx; obtain ⟨p,h',rfl⟩:= List.mem_map.mp hx; exact hs k p (List.mem_toFinset.mpr h')
       choose F b Y hv using fun k=> show ∃ F b Y,(∃ F t y,Θ k F t y)→ Θ k F b Y from (by
              by_cases h:∃ F t y,Θ k F t y; · rcases h with ⟨F,t,y,h⟩; exact ⟨_,_,_,fun _=>h⟩
              exact ⟨Classical.arbitrary _,0,0,fun h'=> (h h').elim⟩)
       have hL:= ht'.mono fun i hi=> hv i hi
       let F' :ℕ→ Fin n→ Fin (Quorum n m):=F; let E(i:ℕ):E4:= digit (α (φ i)) (b i); obtain ⟨⟨p,q⟩,h',f,hf,hr⟩:= ((isCompact_closedBall (0:E4) (3*σ)).prod (isCompact_univ (X:=Fin n→ Fin (Quorum n m)))).tendsto_subseq' (x:=fun i:ℕ=>(E i,F' i)) ((hL.mono fun i hi=>⟨mem_closedBall_zero_iff.mpr hi.1,mem_univ _⟩).frequently)
       have hQ:Tendsto (fun i=> F' (f i)) atTop (𝓝 q):= (continuous_snd.tendsto (p,q)).comp hr; have hK:Tendsto (E ∘ f) atTop (𝓝 p):= (continuous_fst.tendsto (p,q)).comp hr; have hx:= hf.tendsto_atTop.eventually hL; refine ⟨q,p,mem_closedBall_zero_iff.mp h'.1,f,b∘f,fun j i=> Y (f i) j,hf,hK,fun j=>?_,hx.mono (fun i hi=> hi.2.2)⟩
       apply (hK.add_const ((↑(D j+(q j).val):ℝ) • ((2*σ) • basis a))).congr'; filter_upwards [hQ.eventually ((isOpen_discrete (Set.singleton q)).eventually_mem (Set.mem_singleton q)) ,hx] with i hi hp; have hp:= hp.2.1 j; change digit (α (φ (f i))) _= notch (E (f i)) (D j+(F' (f i) j).val) σ a at hp; rw [Set.mem_singleton_iff.mp hi] at hp; exact hp.symm
variable (T:Pollens P Q) (A:EuPin→* (Q.W≃ₗ[ℂ] Q.W))(L: Ortho.Skew→ Q.W→ₗ[ℂ] Q.W)
set_option quotPrecheck false
local notation "Fnz"=>equip T A L
noncomputable abbrev lamp (a: Axis)(s':Bool)(l: List Bond): Cluster (equip T A L):= if s' then reflect (position (Q:=Q) l) a else position l
noncomputable abbrev vitality (a:Axis)(d:Fin n→ℕ)(p:E4) (σ:ℝ)(f:Fin n→I): Strip Q:= (List.ofFn fun i:Fin n=> carry (F:=Fnz) (lamp T A L a (s i) (w (f i))) (Guilt (s i) a p (notch p (d i) σ a))).flatten
omit h hP hφ
open Strip
omit [Fintype I] in
lemma vitality_sy (Y:Fin n→ ℕ→ Cover)(b:ℕ→ Cover)(f:ℕ→ℕ)(d:Fin n→ℕ)(p:E4)(σ:ℝ)(g:Fin n→I)(hr:Involutive (T.adj a)): position (pilfer P (fun i=> (w i).map (onward f)) s b Y a p (fun i=> notch p (d i) σ a) g)= vitality w s T A L a d p σ g:=by
       unfold vitality position pilfer; rw[List.map_flatten,List.map_ofFn]; congr 2; funext i; change position (Q:=Q) (Borne ..) =_; rw [omens _ T A L _ _ _ _ _ _ hr, scent] -- syntax
omit [Fintype I] in
lemma covered (Y:Fin n→ ℕ→ Cover)(b:ℕ→ Cover)(p:E4)(q: Fin n→E4)(hx:∀ j,Worn C φ (w j))(hb:Loc C φ b p)(hq:∀ i, Loc C φ (Y i) (q i))(f:Fin n→I): Worn C φ (pilfer P w s b Y a p q f):=by
       constructor; intro u hu; obtain ⟨l,hl,hu⟩:= List.mem_flatten.mp hu; obtain ⟨k,rfl⟩:= List.mem_ofFn.mp hl; exact (Worn.pastP _ P (s k) a (hx _) hb (hq k)).extended u hu
include h hP hφ hQ
lemma atP (hp:Available P φ w z u σ m)(hW:∀ i:I,Worn C φ (w i))(hv:Involutive (T.adj a)):∃ (F:Fin n→Fin (Quorum n m))(p:E4), ‖p‖≤3*σ ∧ let d(i:Fin n):= D i+(F i).val; (∀ f:Fin n→I, Strip.distinct (vitality w s T A L a d p σ f)) → ‖(∑ f:Fin n→I, wealth s z f * Strip.tone (vitality w s T A L a d p σ f))‖≤ u^n:=by
       obtain ⟨F,p,hx,f,b,Y,hf,ht,hy,H⟩:= pours h hP hφ z w s a D hp; refine ⟨F,p,hx,?_⟩; let w'(i:I):=(w i).map (onward f); intro d hA; let L'(i:Fin n):=notch p (d i) σ a; let Q' := pilfer P w' s b Y a p L'
       have he(g:Fin n→I):position (Q' g)= vitality w s T A L a d p σ g:= vitality_sy _ _ _ _ _ _ _ _ _ _ _ _ _ hv -- syntax
       let W (j:Fin n→I)(i:ℕ):= task P (φ (f i)) (wade (Q' j) i)
       have hQ'(j:Fin n→I):Tendsto (fun i=>(R (φ (f i))).average (W j i)) atTop (𝓝 (tone (vitality w s T A L a d p σ j))):=by
             rw [← he]; exact evaluationS (hQ.tuned hf.tendsto_atTop) _ (covered w' s a Y b p L' (fun i=> Worn.award _ (hW i) hf.tendsto_atTop) ht hy j) ((he j).symm ▸ hA j)
       apply le_of_tendsto (tendsto_finsetSum _ (fun j _=> (hQ' j).const_mul (wealth s z j))|>.norm)
       filter_upwards [H] with i hi; change ‖∑ j:Fin n→I,wealth s z j*_‖ ≤_; apply le_trans (Eq.le ?_) hi; congr 1; unfold cash; rw[map_sum]; apply Finset.sum_congr rfl; intro j hj; rw [map_smul]; congr 1; unfold W Q'; rw [waltz]; unfold w'; simp only[waft]
end YM.Plata
#print axioms YM.Plata.pours
#print axioms YM.Plata.atP
