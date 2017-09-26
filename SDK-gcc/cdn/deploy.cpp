#include "deploy.h"
#include <iostream>
#include <vector>
#include <cstdlib>
#include <cstdio>
#include <string>
#include <cstring>
#include <queue>
#include <stdlib.h>
#include <time.h>
#include <algorithm>
using namespace std;

#define inf INF
#define BIG 900
#define uint unsigned int
/**********全局变量*************/
clock_t start_time,end_time,find_time;
int count_spfa_time=0;
int net_point_number=0;
int net_line_number=0;
int consum_point_number=0;
int server_cost_per = 0;
int width_need=0;
const int MAXN = 1300;
const long int MAXM = 1300*1300;
const int INF = 0x3f3f3f3f;
int totol_level=0;
int totol_level_x=0;
int min_real=INF;
int minest_real = INF;
int min_fixed=INF;

struct node_path
{
    vector<vector<int>>path;
    int total;
}Node_Path[MAXN];

struct node
{
    int u,v,cap,cap_old,cost,next;

}Edge[MAXN<<8];

struct consum_point
{
    int id;
    int connect_id;
    int need_cost;
    consum_point(int s,int e,int c){id = s;connect_id = e;need_cost = c;}
};

struct station_level
{
    int id;
    int capability;
    int cost_per;
}sta_lev[10];

int fixed_cost[MAXN];
int pre[MAXN];          // pre[v] = k：在增广路上，到达点v的边的编号为k
int dis[MAXN];          // dis[u] = d：从起点s到点u的路径长为d
int vis[MAXN];         // inq[u]：点u是否在队列中
int path[MAXN];
int head[MAXN];
int head_old[MAXN];
int abord[MAXN];
int abord_best[MAXN];
int min_cost=0;
int minest_cost=INF;
int width_total=0;
long int NE;
long int old_NE;
long int cost_total=0;
vector<struct consum_point> con_point;
vector<vector<int>>result_queue;

int end_spfa_2(int t,vector<int>&temp_vector);

int select_level(int need)
{
    for(int i=0;i<totol_level;i++)
    {
        if(need<=sta_lev[i].capability)
            return i+1;
    }
    return 0;
}
int get_real_cost(int this_cost,int* station)
{
    int real_cost=this_cost;
    for(int x=0;x<net_point_number;x++)
    {
        if(abord[x]!=0)
        {
            int need = Node_Path[x].total;
            if(need==0)
            {
                real_cost-=(sta_lev[abord[x]-1].cost_per+fixed_cost[x]);
                abord[x]=0;
                continue;
            }
            for(int i=0;i<totol_level;i++)
            {
                if(need<=sta_lev[i].capability)
                {
                    real_cost-=(sta_lev[abord[x]-1].cost_per-sta_lev[i].cost_per);
                    abord[x]=i+1;
                    break;
                }

            }
        }
    }
    return real_cost;
}

/**************spfa图的贪心部分****************/
void addEdge(int u,int v,int cap,int cost)
{
    Edge[NE].u=u;         //边起点
    Edge[NE].v=v;         //边终点
    Edge[NE].cap    =cap;     //边容量
    Edge[NE].cap_old=cap;     //边容量
    Edge[NE].cost=cost;   //边花费
    Edge[NE].next=head[u];//
    head[u]=NE++;//反向边ID
    Edge[NE].v=u;//反向边终点
    Edge[NE].u=v;//反向边起点
    Edge[NE].cap=cap;//反向边容量
    Edge[NE].cap_old=cap;
    Edge[NE].cost=cost;//反向边cost
    Edge[NE].next=head[v];//反向边下一条ID
    head[v]=NE++;//下一边ID
}

void addEdge_new(int u,int v,int cap,int cost)
{
    Edge[NE].u=u;         //边起点
    Edge[NE].v=v;         //边终点
    Edge[NE].cap    =cap;     //边容量
    Edge[NE].cap_old=cap;     //边容量
    Edge[NE].cost=cost;   //边花费
    Edge[NE].next=head[u];//
    head[u]=NE++;//反向边ID
    Edge[NE].v=u;//反向边终点
    Edge[NE].u=v;//反向边起点
    Edge[NE].cap=0;//反向边容量
    Edge[NE].cap_old=0;
    Edge[NE].cost=-cost;//反向边cost
    Edge[NE].next=head[v];//反向边下一条ID
    head[v]=NE++;//下一边ID

    Edge[NE].u=v;         //边起点
    Edge[NE].v=u;         //边终点
    Edge[NE].cap    =cap;     //边容量
    Edge[NE].cap_old=cap;     //边容量
    Edge[NE].cost=cost;   //边花费
    Edge[NE].next=head[v];//
    head[v]=NE++;//反向边ID
    Edge[NE].v=v;//反向边终点
    Edge[NE].u=u;//反向边起点
    Edge[NE].cap=0;//反向边容量
    Edge[NE].cap_old=0;
    Edge[NE].cost=-cost;//反向边cost
    Edge[NE].next=head[u];//反向边下一条ID
    head[u]=NE++;//下一边ID
}

void addEdge_super(int u,int v,int cap,int cost)
{
    Edge[NE].u=u;         //边起点
    Edge[NE].v=v;         //边终点
    Edge[NE].cap=cap;     //边容量
    Edge[NE].cap_old=cap;
    Edge[NE].cost=cost;   //边花费
    Edge[NE].next=head[u];//
    head[u]=NE++;//反向边ID
    Edge[NE].v=u;//反向边终点
    Edge[NE].u=v;//反向边起点
    Edge[NE].cap=0;//反向边容量
    Edge[NE].cap_old=0;
    Edge[NE].cost=cost;//反向边cost
    Edge[NE].next=head[v];//反向边下一条ID
    head[v]=NE++;//下一边ID
}
void addEdge_super_2(int u,int v,int cap,int cost)
{
    Edge[NE].u=u;         //边起点
    Edge[NE].v=v;         //边终点
    Edge[NE].cap=cap;     //边容量
    Edge[NE].cap_old=cap;
    Edge[NE].cost=cost;   //边花费
    Edge[NE].next=head[u];//
    head[u]=NE++;//反向边ID

    Edge[NE].v=u;//反向边终点
    Edge[NE].u=v;//反向边起点
    Edge[NE].cap=0;//反向边容量
    Edge[NE].cap_old=0;
    Edge[NE].cost=INF;//反向边cost
    Edge[NE].next=head[v];//反向边下一条ID
    head[v]=NE++;//下一边ID
}

/******************spfa费用流部分****************/
void reback_for_sub(vector< int> fix_vec,vector< vector<int>> path_this_all)
{
    for(uint i=0;i<fix_vec.size();i++)
    {
        if(fix_vec[i]<old_NE)
        {
            Edge[fix_vec[i]].cap  = Edge[fix_vec[i]].cap_old;
        }
    }
    for(uint i=0;i<path_this_all.size();i++)
    {
        int temp_u=path_this_all[i][path_this_all[i].size()-1];
        path_this_all[i].pop_back();
        Node_Path[temp_u].total-=path_this_all[i][path_this_all[i].size()-1];
        width_total-=path_this_all[i][path_this_all[i].size()-1];
    }
}

void release_node(int release,int &now_sum)
{
    int tiaoshu = Node_Path[release].path.size();
    for(int i=0;i<tiaoshu;i++)
    {
        int bianshu = Node_Path[release].path[i].size();
        int liu = Node_Path[release].path[i][bianshu-1];
        for(int j=0;j<bianshu-1;j++)
        {
            int path_id = Node_Path[release].path[i][j];
            Edge[path_id].cap+=liu;
            Edge[path_id].cap_old+=liu;
            now_sum-=liu*Edge[path_id].cost;
        }
        Node_Path[release].total-=liu;
        width_total-=liu;
    }
}

void callback_node(int release)
{
    int tiaoshu = Node_Path[release].path.size();
    for(int i=0;i<tiaoshu;i++)
    {
        int bianshu = Node_Path[release].path[i].size();
        int liu = Node_Path[release].path[i][bianshu-1];
        for(int j=0;j<bianshu-1;j++)
        {
            int path_id = Node_Path[release].path[i][j];
            Edge[path_id].cap-=liu;
            Edge[path_id].cap_old-=liu;
        }
        Node_Path[release].total+=liu;
        width_total+=liu;
    }
}

int SPFA_for_sub(int t,int release)                   //  源点为0，汇点为sink。
{
    int i;
    memset(dis,inf,sizeof(dis));
    memset(vis,0,sizeof(vis));
    memset(pre,-1,sizeof(pre));
    queue<int>q;
    for(int i=0;i<net_point_number;i++)
    {
        if(abord[i]!=0&&Node_Path[i].total<sta_lev[abord[i]-1].capability)
        {
            dis[i] = 0;//源点到自己距离为0
            q.push(i);//压入源点
            vis[i] =1;//源点在队列中
        }
    }
    while(!q.empty())        //  这里最好用队列，有广搜的意思，堆栈像深搜。
    {
        int u =q.front();
        q.pop(); vis[u] =0;//u已经出队列
        if(dis[u]>=dis[t])
        {
           continue;
        }
        for(i=head[u]; i!=-1;i=Edge[i].next)//增广过程，不断寻找下个路径
        {
            int v=Edge[i].v;

            if(Edge[i].cap >0&& dis[v]>dis[u]+Edge[i].cost)
            {
                dis[v] = dis[u] + Edge[i].cost;//更新v的距离为更短的距离：u的距离加uv边权
                pre[v] = u;                    //更新v的前向节点为u
                path[v]=i;                     //v
                if(!vis[v])                    //如果v不在队列中，压入v
                {
                    vis[v] =1;
                    q.push(v);
                }
            }
        }
    }
    if(dis[t] == inf)
        return false;
    return true;
}
int end_spfa_for_sub(int t,vector< int>&fix_vec,vector<int>&path_this,bool choose=0)
{
    int u, sum = inf,per_cost=0;
    for(u=t; pre[u]!=-1; u=pre[u])
    {
        sum = min(sum,Edge[path[u]].cap);//沿着已寻找好的路径遍历，找到路径中边的最小容量
        per_cost+=Edge[path[u]].cost;
        fix_vec.push_back(path[u]);
        path_this.push_back(path[u]);
    }

    sum = min(sum,sta_lev[abord[u]-1].capability-Node_Path[u].total);
    path_this.push_back(sum);
    path_this.push_back(u);
    Node_Path[u].total+=sum;
    width_total+=sum;
    for(u = t; pre[u] != -1; u=pre[u])//
    {
        Edge[path[u]].cap -= sum;
        if(choose==1)
            Edge[path[u]].cap_old -= sum;
    }
    return sum*per_cost;
}

/***********************************************/
bool cost_flow_for_sub(bool state,int release,int now_sum, bool choose)
{
    int old_abord_lev = abord[release];
    abord[release]=0;//把当前站，变为非站
    vector< int>fix_vec;
    int this_sum = now_sum;
    now_sum-=(sta_lev[old_abord_lev-1].cost_per+fixed_cost[release]);//sta_lev[station[release]-1].cost_per+fixed_cost[release];
    release_node(release,now_sum);
    //int old_width=width_total;
    vector<vector<int>>path_this_all;
    while(SPFA_for_sub(net_point_number,release))
    {
        vector<int>path_this;
        now_sum+=end_spfa_for_sub(net_point_number,fix_vec,path_this,choose);
        path_this_all.push_back(path_this);
        if(now_sum>min_cost)
        {
            abord[release]=old_abord_lev;
            now_sum=this_sum;
            reback_for_sub(fix_vec,path_this_all);
            callback_node(release);
            return false;
        }
    }

    if(width_need!=width_total)
    {
        if(width_need>width_total&&choose==1)
            cout<<"need: "<<width_need<<" get: "<<width_total<<endl;
        abord[release]=old_abord_lev;
        //width_total=old_width;
        now_sum=this_sum;
        reback_for_sub(fix_vec,path_this_all);
        callback_node(release);

        return false;
    }
    min_cost=now_sum;
    if(choose==0)
    {
        abord[release]=old_abord_lev;
        //width_total=old_width;
        now_sum=this_sum;
        reback_for_sub(fix_vec,path_this_all);
        callback_node(release);
        return true;
    }
    for(uint i=0;i<path_this_all.size();i++)
    {
        int temp_u=path_this_all[i][path_this_all[i].size()-1];
        path_this_all[i].pop_back();
        Node_Path[temp_u].path.push_back(path_this_all[i]);
        Node_Path[temp_u].total+=path_this_all[i][path_this_all[i].size()-1];
    }
    vector<vector<int>> ().swap(Node_Path[release].path);
    cout<<"find better: "<<min_cost<<endl;;

    return true;
}


void format_for_sub(char * topo[MAX_EDGE_NUM], int line_num)
{
    int s=0, e=0, t=0, c=0;
    sscanf(topo[0],"%d %d %d", &net_point_number, &net_line_number, &consum_point_number);//第一行数据：全图的点数，边数，消费节点个数
    //sscanf(topo[2],"%d", &server_cost_per);//第三行数据：每设置一个消费节点的需要的花费
    long int i = 2;//控制读入行数的变量
    for(; topo[i][0]!='\r'; i++)
    {
        sscanf(topo[i], "%d %d %d", &s, &e, &t);//读入：服务器层级，输出能力，花销
        sta_lev[i-2].id=s;
        sta_lev[i-2].capability=e;
        sta_lev[i-2].cost_per=t;
        totol_level++;
    }
    totol_level_x = totol_level;
    totol_level=6;
    i++;
    for(; topo[i][0]!='\r'; i++)
    {
        sscanf(topo[i], "%d %d", &s, &e);//读入：点ID，点花费
        fixed_cost[s]=e;
        if(min_fixed>e)
            min_fixed=e;
    }
    i++;
    for(; topo[i][0]!='\r'; i++)
    {
        sscanf(topo[i], "%d %d %d %d", &s, &e, &t, &c);//读入：边起点，边终点，边带宽，边消费
        addEdge(s,e,t,c);//构造整张图的拓扑网络
    }

    i++;
    server_cost_per=sta_lev[totol_level-1].cost_per;
    for(; i < line_num; i++)
    {
        sscanf(topo[i], "%d %d %d", &s, &e, &c);//读入：消费节点ID，与消费节点相连的点的ID，该消费节点的需求
        consum_point* temp = new consum_point(s,e,c);//消费节点的数据结构是结构体，所以以NEW的方式生成
        con_point.push_back(*temp);//把当前读入的消费节点信息压入容器中保存
        width_need+=c;//计算总需求，以备计算费用流时检测需求满足情况
        addEdge_super(e,net_point_number,0,0);//构造该消费节点到超级汇点的边，超级汇点的编号为总点数的数值，边容量本身应该为消费节点的需求量，但这里设置为0，意味着由该需求点上安置的站点提供了需求的流量，所以容量为0，边花费为0，意味最短路会优先选择走该条路
        vector<int> temp_this;//保存住每个消费节点放一个站时，流量的路径以及流量值，以供稍后释放
        temp_this.push_back(NE-2);//初试情况下，由于直接在与消费节点相连的普通节点上放站，相当于从该站出发的路径只有一条
        temp_this.push_back(c);//初试情况下，由于直接在与消费节点相连的普通节点上放站，相当于从该站出发的流量为该消费节点的需求c
        Node_Path[e].path.push_back(temp_this);//把流量路径和流量值存入到对应的站点结构体里
        abord[e]=totol_level;//select_level(c);//abord是长度为节点数的数组，对应位置为1说明在该点放了站
        min_cost+=fixed_cost[e]+sta_lev[abord[e]-1].cost_per;
        Node_Path[e].total=c;
    }
    width_total=width_need;//初始化当前总流量为总体需求的流量，因为每个消费点已经放了一个站，所以总流量与需要的流量是一样的

}


/******************spfa费用流随机部分****************/
void reback(vector< int> fix_vec,int count_station)
{
    for(uint i=0;i<fix_vec.size();i++)
        Edge[fix_vec[i]].cap  = Edge[fix_vec[i]].cap_old;
    width_total=0;
}


int SPFA(int t,int*station)                   //  源点为0，汇点为sink。
{
    int i;

    memset(dis,inf,sizeof(dis));
    memset(vis,0,sizeof(vis));
    memset(pre,-1,sizeof(pre));
    queue<int>q;
    for(int i=0;i<net_point_number;i++)
    {
        if(station[i]!=0&&Node_Path[i].total<sta_lev[station[i]-1].capability)
        {
            dis[i] = 0;//源点到自己距离为0
            q.push(i);//压入源点
            vis[i] =1;//源点在队列中
        }
    }
    while(!q.empty())        //  这里最好用队列，有广搜的意思，堆栈像深搜。
    {
        int u =q.front();
        q.pop(); vis[u] =0;  //u已经出队列
        if(dis[u]>=dis[t])
        {
           continue;
        }
        for(i=head[u]; i!=-1;i=Edge[i].next)//增广过程，不断寻找下个路径
        {
            int v=Edge[i].v;

            if(Edge[i].cap >0&& dis[v]>dis[u]+Edge[i].cost)
            {
                dis[v] = dis[u] + Edge[i].cost;//更新v的距离为更短的距离：u的距离加uv边权
                pre[v] = u;                    //更新v的前向节点为u
                path[v]=i;                     //v
                if(!vis[v])                    //如果v不在队列中，压入v
                {
                    vis[v] =1;
                    q.push(v);
                }
            }
        }
    }

    if(dis[t] == inf)
        return false;
    return true;
}

int end_spfa(int* station,int t,vector< int>&fix_vec)
{
    int u, sum = inf,per_cost=0;
    for(u=t; pre[u]!=-1; u=pre[u])
    {
        sum = min(sum,Edge[path[u]].cap);//沿着已寻找好的路径遍历，找到路径中边的最小容量
        per_cost+=Edge[path[u]].cost;
        fix_vec.push_back(path[u]);
    }
    sum = min(sum,sta_lev[station[u]-1].capability-Node_Path[u].total);
    Node_Path[u].total+=sum;
    width_total+=sum;

    for(u = t; pre[u] != -1; u=pre[u])//
    {
        Edge[path[u]].cap -= sum;
    }
    return sum*per_cost;

}

int end_spfa_for_add(int t)
{
    int u, sum = inf,per_cost=0;
    vector<int>path_this;
    for(u=t; pre[u]!=-1; u=pre[u])
    {

        sum = min(sum,Edge[path[u]].cap);//沿着已寻找好的路径遍历，找到路径中边的最小容量
        per_cost+=Edge[path[u]].cost;
        path_this.push_back(path[u]);
    }
    //sum = min(sum,Edge[path[u]].cap);
    sum = min(sum,sta_lev[abord[u]-1].capability-Node_Path[u].total);
    path_this.push_back(sum);
    Node_Path[u].path.push_back(path_this);
    Node_Path[u].total+=sum;
    width_total+=sum;
    for(u = t; pre[u] != -1; u=pre[u])//
    {
        Edge[path[u]].cap -= sum;
        Edge[path[u]].cap_old -= sum;
    }
    return sum*per_cost;

}

bool cost_flow_for_add(int *station)
{
    int now_sum=0;
    width_total=0;
    memset(Node_Path,0,sizeof(Node_Path));

    for(int x = 0;x<net_point_number;x++)
    {
        if(station[x]!=0)
        {
            now_sum+=sta_lev[station[x]-1].cost_per+fixed_cost[x];
        }
    }

    while(SPFA(net_point_number,station))
    {
        now_sum+=end_spfa_for_add(net_point_number);
    }

    min_cost=now_sum;

    cout<<" minest: "<<minest_cost<<" width: "<<width_total<<endl;

    return true;
}


bool cost_flow_for_final(int *station)
{
    int now_sum=0;
    width_total=0;
    memset(Node_Path,0,sizeof(Node_Path));

    for(int x = 0;x<net_point_number;x++)
    {
        if(station[x]!=0)
        {
            cout<<x<<" ";
            now_sum+=sta_lev[station[x]-1].cost_per+fixed_cost[x];
        }
    }
    cout<<endl;

    while(SPFA(net_point_number,station))
    {
        vector<int>temp;
        now_sum+=end_spfa_2(net_point_number,temp);
    }

    min_cost=now_sum;

    cout<<" minest: "<<minest_cost<<" final: "<<width_total<<endl;

    return true;
}

/*******************************************/
int end_spfa_2(int t,vector<int>&temp_vector)
{
    int u, sum = inf,per_cost=0;
    vector<int>path_this;
    for(u=t; pre[u]!=-1; u=pre[u])
    {
        sum = min(sum,Edge[path[u]].cap);//沿着已寻找好的路径遍历，找到路径中边的最小容量
        per_cost+=Edge[path[u]].cost;
        temp_vector.push_back(Edge[path[u]].v);
    }
    temp_vector.push_back(Edge[path[u]].v);
    sum = min(sum,sta_lev[abord_best[u]-1].capability-Node_Path[u].total);
    Node_Path[u].path.push_back(path_this);
    temp_vector.push_back(sum);
    result_queue.push_back(temp_vector);
    Node_Path[u].total+=sum;
    width_total+=sum;

                     //记录最大流
    for(u = t; pre[u] != -1; u=pre[u])//
    {
        Edge[path[u]].cap -= sum;
        Edge[path[u]].cap_old -= sum;
    }
    //Edge[path[u]].cap -= sum;
    return sum*per_cost;
}


void format(char * topo[MAX_EDGE_NUM], int line_num)
{
    int s=0, e=0, t=0, c=0;
    sscanf(topo[0],"%d %d %d", &net_point_number, &net_line_number, &consum_point_number);//第一行数据：全图的点数，边数，消费节点个数
    //sscanf(topo[2],"%d", &server_cost_per);//第三行数据：每设置一个消费节点的需要的花费
    long int i = 2;//控制读入行数的变量
    for(; topo[i][0]!='\r'; i++)
    {

    }
    i++;
    for(; topo[i][0]!='\r'; i++)
    {

    }
    i++;
    for(; topo[i][0]!='\r'; i++)
    {
        sscanf(topo[i], "%d %d %d %d", &s, &e, &t, &c);//读入：边起点，边终点，边带宽，边消费
        addEdge(s,e,t,c);//构造整张图的拓扑网络
    }

    i++;
    for(; i < line_num; i++)
    {
        sscanf(topo[i], "%d %d %d", &s, &e, &c);//读入：消费节点ID，与消费节点相连的点的ID，该消费节点的需求

        addEdge_super(e,net_point_number,c,0);//构造该消费节点到超级汇点的边，超级汇点的编号为总点数的数值，边容量本身应该为消费节点的需求量，但这里设置为0，意味着由该需求点上安置的站点提供了需求的流量，所以容量为0，边花费为0，意味最短路会优先选择走该条路
    }
}

/***********************************************/
bool cost_flow(int*station,bool state,int count_10s)
{
    count_spfa_time++;
    vector< int>fix_vec;
    int now_sum=0;
    int count_station=0;
    NE=old_NE;
    memset(Node_Path,0,sizeof(Node_Path));
    for(int x = 0;x<net_point_number;x++)
    {
        if(abord[x]!=0)
        {
            count_station++;
            now_sum+=sta_lev[abord[x]-1].cost_per+fixed_cost[x];
        }
    }

    while(SPFA(net_point_number,abord))
    {
        now_sum+=end_spfa(abord,net_point_number,fix_vec);
        //int temp_real = get_real_cost(now_sum,station);
        if(now_sum>=min_real&&!state)
        {
            reback(fix_vec,count_station);
            return false;
        }
    }

    if(width_need!=width_total)
    {
        reback(fix_vec,count_station);

        return false;
    }
    min_cost=now_sum;
    int this_real=now_sum;
    if(state==1)
        this_real=get_real_cost(now_sum,abord);
    if(this_real>=min_real)
    {
        reback(fix_vec,count_station);
        return false;
    }
    else
    {
        min_real=this_real;
    }

    if(min_real<minest_real)
    {
        minest_real = min_real;

        memcpy(abord_best,abord,sizeof(abord));
       // memcpy(abord,station,sizeof(abord));

    }

    //cout<<"find better: "<<min_real<<" min_cost:"<<now_sum<<endl;
    reback(fix_vec,count_station);
    return true;
}


//你要完成的功能总入口
void deploy_server(char * topo[MAX_EDGE_NUM], int line_num,char * filename)
{
    double dur=0;   //全局计时变量，用于控制程序退出，以免运行超时
    double new_dur;//短时间计时变量，用于让程序在一段时间内找不到更优解时，接受一个差一点的解
    bool state=0;  //控制状态变量，程序在一段时间内找不到更优解时，将该变量置1，表示要接受一个差一点的解
    double stop_time=20;//不断减少站数目策略的时间控制，过了该时间，采用新的加减交换策略，不同大小案例该值不同

    start_time = clock();  //程序起始时间
    srand((unsigned)time(NULL));//生成初始随机种子，用于后面各种生成随机数的场合，以时间为种子

    memset(head,-1,sizeof(head));//初始化所有点的前向星链表为-1
    memset(head_old,-1,sizeof(head_old));//初始化用于保存所有点的前向星链表的旧状态的数组为-1
    memset(Node_Path,0,sizeof(Node_Path));
    format_for_sub(topo,line_num);//为减站策略初始化整张图，topo是系统读入的赛题数据，line_num没啥用
    memcpy(head_old,head,sizeof(head[1])*(net_point_number+1));

    old_NE=NE;//保存住当前全部添加的边数，其实在这里暂时没啥用
    //min_cost += server_cost_per*consum_point_number;//当前最小的消费就是消费节点的个数乘上单个视频站的费用，因为初始可行解为每个消费节点放个站
   // int count_loop=0;

        /*************************************************/
    for(int wai=consum_point_number;wai>0;wai--)//外层循环，控制删点的次数，理论上删点的个数不得超过总点数，实际上可删点比总点数少的多
    {
        int best_choose=-1;//初始化当前最优可被删的点ID为-1，待循环结束，如果此值还是-1说明没法删点了，该加点了
        int this_cost=min_cost;//当前情况下的花费最小值
        /****************删点********************/
        for(int nei=0;nei<net_point_number;nei++)//对每一个点遍历
        {
            int temp = nei ;
            if(abord[temp]==0)//如果当前点是非站，则进行下一次循环，不对当前点操作
                continue;

            bool res=cost_flow_for_sub(state,temp,this_cost,0);//进行一次费用流运算，最后一个参数为0代表这个站只是试删一下获取费用，还会还原这个站

            if(res)//res为1说明删除这个点后总体的费用是目前效果最好的，则更新这层最优的删除点为此点
                best_choose=temp;
        }
        if(best_choose!=-1)//若此层遍历完毕，最优可删点ID不是-1,
            cost_flow_for_sub(state,best_choose,this_cost,1);//以更改后的站点分布数组做一次费用流，最后一个参数是1代表确定删除此点，不会恢复它
        else//若此层遍历完毕，最优可删点ID是-1,说明删除任何点都不好，则跳出循环，准备加些站点进去
            break;
    }
    cout<<"last minest:"<<min_cost<<endl;

    memcpy(abord_best,abord,sizeof(abord[1])*net_point_number);
    minest_cost=min_cost;


/***************************************************************/
    memset(head,-1,sizeof(head));
    memset(head_old,-1,sizeof(head_old));
    NE=0;
    format(topo,line_num);
    old_NE=NE;
    memcpy(head_old,head,sizeof(head[1])*(net_point_number+1));
    memcpy(abord,abord_best,sizeof(abord_best));
    cost_flow(abord,1,0);//这里的cost_flow用法与上面会有不同，没有释放流量的步骤
    minest_cost=min_cost;


    /********************简单禁忌表*******************/
    int count_10s=0;//这个变量用于控制是否经过一段时间没有找到最优值，找到时要清除该变量为0
    state=0;//如果需要接受一个差一点的值以供跳出局部最优，就把state变量置位
    int loop_time=30;
    if(net_point_number>BIG)
        loop_time=70;
    find_time = clock();
    /*************************************************/
    for(;dur/CLOCKS_PER_SEC<88;)
    {
        end_time = clock();
        dur = (double)(end_time - start_time);
        new_dur = (double)(end_time - find_time);

        if(new_dur/CLOCKS_PER_SEC>5)
        {
            count_10s++;
            find_time = clock();
        }
        int temp ;
        int old;
        bool res=0;

        /****************删点********************/
        if(dur/CLOCKS_PER_SEC>loop_time){
            state=1;
            temp =  rand() % net_point_number;
            while(abord[temp]==0||Node_Path[temp].total==sta_lev[abord[temp]-1].capability)
            {
                temp =  rand() % net_point_number;
            }
            old=abord[temp];
            abord[temp]=0;
            res = cost_flow(abord,state,count_10s);
            if(res)
            {
                count_10s=0;
                find_time = clock();
                clock_t this_time = clock();
                double temp_dur = (double)(this_time - start_time);
                cout<<temp_dur/CLOCKS_PER_SEC<<" find "<<min_real<<" by remove point, minest:"<<minest_real<<endl;
            }
            else
            {
                abord[temp]=old;
            }
        }
        /****************交换点**********************/
        //if(dur/CLOCKS_PER_SEC<10*loop_time&&net_point_number>BIG)
          //  continue;
        int temp2 =  rand() % net_point_number;
        while(abord[temp2]==0)
        {
            temp2 =  rand() % net_point_number;
        }
        vector<int>neighbor;
        //i=head[u]; i!=-1;i=Edge[i].next
        if(net_point_number<BIG)
        {
            for(int x = head[temp2];x!=-1;x = Edge[x].next)
            {
                if(Edge[x].v!=net_point_number&&abord[Edge[x].v]==0&&fixed_cost[temp2]>=fixed_cost[Edge[x].v])

                    neighbor.push_back(Edge[x].v);
            }
        }
        else
        {
             for(int x = head[temp2];x!=-1;x = Edge[x].next)
            {
                if(Edge[x].v!=net_point_number&&abord[Edge[x].v]==0&&fixed_cost[temp2]>fixed_cost[Edge[x].v])

                    neighbor.push_back(Edge[x].v);
            }
        }
        if(neighbor.size()==0)
            continue;
        int temp_random = rand() % neighbor.size();
        int temp1 = neighbor[temp_random];
        swap(abord[temp1],abord[temp2]);

        if(new_dur/CLOCKS_PER_SEC>5)
        {
            count_10s++;
            find_time = clock();
        }

        res = cost_flow(abord,state,count_10s);
        if(res)
        {
            count_10s=0;
            clock_t this_time = clock();
            double temp_dur = (double)(this_time - start_time);
            cout<<temp_dur/CLOCKS_PER_SEC<<" find "<<min_real<<" by swap point, minest:"<<minest_real<<endl;
            find_time = clock();
             continue;
        }
        else
            swap(abord[temp1],abord[temp2]);
    }
    cout<<"reach 88s"<<endl;
    int now_sum_final=0;
    width_total=0;
    NE=old_NE;
    memset(Node_Path,0,sizeof(Node_Path));
    for(int x = 0;x<net_point_number;x++)
    {
        if(abord_best[x]!=0)
        {
            now_sum_final+=sta_lev[abord_best[x]-1].cost_per+fixed_cost[x];
            cout<<x<<" ";
        }
    }
    cout<<endl;

    while(SPFA(net_point_number,abord_best))
    {
        vector<int>temp_vector;
        now_sum_final+=end_spfa_2(net_point_number,temp_vector);
    }
    cout<<"now_sum_final = "<<now_sum_final<<endl;
    now_sum_final = get_real_cost(now_sum_final,abord_best);
    for(int i=0;i<net_point_number;i++)
    {
        if(abord_best[i]!=0)
        {
            cout<<i<<" cout "<<Node_Path[i].total;
            abord_best[i] = select_level(Node_Path[i].total);
            cout<<"    "<<abord_best[i]-1<<endl;
        }
    }
/**********************************************************************/
	char  temp_str[60000];
	sprintf(temp_str,"%ld\n\n",result_queue.size());

	for(int x=result_queue.size()-1;x>=0;x--)
	{
        int mySize = result_queue[x].size();
        for(int y=result_queue[x].size()-2;y>0;y--)
        {
            char  temp_no[10];
            sprintf(temp_no,"%d ",result_queue[x][y]);
            strcat(temp_str,temp_no);
            if(y==1)
            {
                int temp_id;
                for(uint c = 0;c< con_point.size();c++)
                {
                    if(con_point[c].connect_id==result_queue[x][y])
                    {
                        temp_id=con_point[c].id;
                        break;
                    }
                }
                char  temp_no[10];
                sprintf(temp_no,"%d",temp_id);
                strcat(temp_str,temp_no);
                continue;
            }
        }
        char  temp_no[10];
        sprintf(temp_no," %d %d",result_queue[x][mySize-1],abord_best[result_queue[x][mySize-2]]-1);
        strcat(temp_str,temp_no);
        if(x!=0)
            strcat(temp_str,"\n");
	}

/**********************************************************************/

	cout<<"need width = "<<width_need<<"time = "<<width_total<<" real res = "<<now_sum_final<<endl;
	char * topo_file = temp_str;
	// 直接调用输出文件的方法输出到指定文件中(ps请注意格式的正确性，如果有解，第一行只有一个数据；第二行为空；第三行开始才是具体的数据，数据之间用一个空格分隔开)
	write_result(topo_file, filename);
}
