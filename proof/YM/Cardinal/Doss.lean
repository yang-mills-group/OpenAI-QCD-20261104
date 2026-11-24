import YM.Cardinal.Sofas
/-! # Singleton report tape, parity generalized. With mask bill requiring on-mask sizes only. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Plate
open QCD Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph QCD.GasP PhysicalNext.Repeat.Turn Patron Kites Ribbon Cupola Relight Ruby
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c f L:Side}{m k l N:ℕ} {I J U E:Type}[Fintype I]
variable {a A C v w t t₁ t₂:ℝ}{O: BudgetPoint}
namespace Card
namespace Iris
variable {q:Bool} (N)(o:Site c)
local notation "M"=> Ribbon.ample N Unit
local notation "T"=> topM
local notation "Vk"=> goldM q
local notation "K"=> Keys c N
local notation "R"=> Spine Iris.alpha
local notation "B!"=>Patio (Keys c N ⊕ Spine Unit)
local notation "p!"=>pluck K (goldM q)
set_option quotPrecheck false
open QCD.Stew
-- Singleton Report coefficients. products of markers vanish. Film.Linearity pack free.C
open NormedSpace
variable (F: Patron.Rail c N E)(Y:Film c N Unit J)(S:Support c)
variable (V:Grid c)
instance (c:Side) : Finite (Cove.Hat c):=Finite.of_injective (f:=fun p:Cove.Hat c=> (p.place,p.inv)) (by rintro ⟨i,t,h1,h2⟩ ⟨j,s,h3,h4⟩ h; obtain ⟨rfl,rfl⟩:=Prod.mk.inj h; rfl)
noncomputable local instance : Fintype (Cove.Hat c):=Fintype.ofFinite _
local notation "N'"=> banknote N (fun _:Unit=>o) v
local notation "E⁺"=>rootR R K
local notation "Q" x=>∑ i:Finset (Cove.Hat c), Plate.roof id x (RG.flags t V) i
lemma gas_meter (h₁:Summable fun i=>‖F.warp i V‖)(h₂:Summable fun i=>‖Y.mark i V‖):
   Film.reports N Y F t V = ∑ i:Finset (Cove.Hat c),Plate.roof id (fun j=>E⁺ (coin F.addr (fun i=>F.warp i V) j)+coin Y.addr (fun i=>Y.mark i V) j) (RG.flags t V) i:=by
    let J' i:=F.warp i V; let H i:=Y.mark i V; let f (i:E⊕J):= Film.spruced N Y F i V; have hp:= Film.payable (E⁺).toLinearMap.toContinuousLinearMap h₁; have he: Summable (fun i=> ‖f i‖) := Summable.sum _ hp h₂
    rw [Film.reports,catalogue _ f _ he,tsum_fintype]; apply congr_arg; funext _i; apply congr_arg (fun (x:Cove.Hat c→ Patio (Keys c N⊕Spine Unit))=> Plate.roof id x (RG.flags t V) _i); funext i; rw [show coin (Film.addressSets N Y F) f i= _ from Film.coin_merge F.addr Y.addr (E⁺ ∘ J') H hp h₂ i, show coin F.addr (E⁺ ∘ J') i=_ from readycoin F.addr J' i (E⁺).toLinearMap.toContinuousLinearMap h₁]; rfl
variable (q:Bool)
lemma honor_exp (x:B!)(hx:Polite (fun _:Unit=>q) T x): NormedSpace.exp x=1+x:=by
    have h: x*x=0:= hx.nilpotent hx (by simp [topM]); have he: x^2=0:= sq x ▸ h -- sq x statement
    rw [← HasSum.tsum_eq (exp_series_hasSum_exp' (𝕂:=ℂ) x), tsum_eq_sum (s:=range 2)]; norm_num [Finset.sum_range_succ, NormedSpace.expSeries_apply_eq] -- inspect
    intro i hi; have hp:2 ≤ i:= Nat.le_of_not_gt fun h=> hi (mem_range.mpr h); simp only [pow_eq_zero_of_le hp he, smul_zero]
lemma rootE (x: EvenA c N): Polite (fun _:Unit=>q) ∅ (E⁺ x):=by unfold Polite; rw [burst_absent]; exact ⟨_,quiet ..⟩
variable {q}
-- variation coefficient.Passion any marker.Unit.Sample.Lift.Spin.
variable {Y}
lemma itt (z:Finset Unit)(h:z.Nonempty): z=T:=by obtain ⟨u,h⟩:=h; ext i; rw [show i=u from Subsingleton.elim ..]; exact iff_of_true h (mem_singleton.mpr (Subsingleton.elim ..)) -- edit
noncomputable def billK (u: Cove.Hat c→ B!)(g:Cove.Hat c→ B!) (p:Finset (Cove.Hat c))(W:Support c): B! := if Arm id W p then ∑ i∈p,g i * ∏ j∈p.erase i,u j else 0
lemma legal_add (g:Cove.Hat c→ B!)(p:Cove.Hat c→ B!)(T₀:Finset (Cove.Hat c))(hp:∀ i,Polite (fun _:alpha=>q) ∅ (g i))(ht:∀ i,Polite (fun _:alpha=>q) topM (p i)) (D: Support c) : Plate.roof id (g+p) D T₀= Plate.roof id g D T₀+billK N g p T₀ D ∧ Polite (fun _:alpha=>q) topM (billK N g p T₀ D):=by
   let v (x:B!):= Polite (fun _:alpha=>q) T x; let X:=T₀; let φ:= fun X: Finset (Hat c)=> ∑ i∈X,p i*∏ j∈X.erase i,g j; have ho(X:Finset _): Polite (fun _:alpha=>q) ∅ (∏ i∈X,g i):=by induction X using Finset.induction_on with| empty=>rw [prod_empty]; exact polite_empty_one _| insert i z h ih=>rw [prod_insert h]; exact (empty_union (∅:Finset alpha)) ▸ (hp i).attached ih
   have hφ(X:Finset _): v (φ X):=by unfold v φ Polite; rw [map_sum]; refine Submodule.sum_mem _ ?_; intro i hi; change Polite (fun _:alpha=> q) T _; have hξ:= (ht i).attached (ho (X.erase i)); have he:∀ (D:Type)[DecidableEq D](S:Finset D),S∪∅=S:= fun _ _ x=> union_empty _; exact Eq.mp (congr_arg (fun s=> Polite (fun _:alpha=>q) s (p i*∏ j∈X.erase i,g j)) (@he _ (Classical.decEq _) _)) hξ
   unfold Plate.roof billK; split; next h=> refine ⟨?_,hφ _⟩; change (∏ i∈T₀,(g+p) i)= _ + φ T₀; clear h; induction T₀ using Finset.induction_on with
           |empty=>simp [φ]
           |insert i z h ih=>
             rw [prod_insert h, prod_insert h,ih, Pi.add_apply,add_mul,mul_add,mul_add, (show p i*φ z=0 from (ht i).nilpotent (hφ _) (by simp [topM])),add_zero]; unfold φ; rw [sum_insert h, erase_insert h, Finset.mul_sum];
             have hx: ∑ j∈ z,p j * (∏ k∈(insert i z).erase j,g k)= ∑ j∈z,g i*(p j* ∏ k∈z.erase j,g k):=sum_congr rfl fun j hj=> by rw [erase_insert_of_ne (ne_of_mem_of_not_mem hj h).symm,prod_insert (fun hi=>h (mem_of_mem_erase hi))]; ring
             rw [hx]; ring
   next h=> exact ⟨(zero_add _).symm,polite_nil ..⟩
variable (D:Grid c→ EvenA c N)(Y)
noncomputable def Ecover : B!:= E⁺ ((NormedSpace.exp (D V))*(Kites.heartK F t V))
noncomputable def Wcall : B!:= ∑ i:Finset (Cove.Hat c), billK N (fun j=>rootR (Spine Unit) (Keys c N) (coin F.addr (fun i=>F.warp i V) j)) (coin Y.addr (fun i=>Y.mark i V)) i (RG.flags t V)
local notation "e₀"=> E⁺ (Kites.heartK F t V)
local notation "W₀"=> Wcall N F Y V (t:=t)
lemma scores (he:Y.Beat N (fun _:Unit=>o) (fun _:alpha=>q) t)(h:Summable fun i=>‖Y.mark i V‖)(hP:Summable fun i=>‖F.warp i V‖) : Film.reports N Y F t V=e₀+W₀ ∧ Polite (fun _: Unit=>q) T W₀:=by
    let g(C:Cove.Hat c):= E⁺ (coin F.addr (fun i=>F.warp i V) C); let p:=coin Y.addr (fun i=>Y.mark i V)
    have hp(i): Polite (fun _:Unit=>q) T (p i):=polite_tsum (fun k=> (itt _ (he.commits _)) ▸ (he.budget k.val V).1)
    let W:= RG.flags t V; let f i:= Plate.roof id g W i; let x i:= billK N g p i W; have hx(i:Finset (Cove.Hat c)):= legal_add N g p i (fun _=>rootE N q _) hp W
    refine ⟨?_,?_⟩
    · rw [gas_meter N F Y V hP h]; change (∑ i: Finset (Hat c), Plate.roof id (g+p) W i)=e₀+ W₀; simp_rw [fun i=>(hx i).1,sum_add_distrib]; apply congr_arg₂ (·+·) _ rfl; rw [goodsK F t V hP,tsum_fintype,map_sum]; refine sum_congr rfl fun i _=>?_ ; unfold Plate.roof; split; exact (map_prod (E⁺) ..).symm; exact (map_zero _).symm
    apply polite_sumX _ (fun i _=>(hx i).2) -- edit
 where
    polite_sumX (F:Finset (Hat c)→B!)(h:∀ i∈(univ:Finset _), Polite (fun _:Unit=>q) T (F i)) : Polite (fun _:Unit=>q) T (∑ i∈univ,F i):=by unfold Polite; rw [map_sum]; exact Submodule.sum_mem _ h
end Iris
end Card
end YM.MassiveQCD.Plate
#print axioms YM.MassiveQCD.Plate.Card.Iris.scores
