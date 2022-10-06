import React, {useEffect, useState} from "react";
import {Link} from "react-router-dom";
import CustomTable from "../../common-components/CustomTable";
import DiscordInfo from "./DiscordInfo";
import fetchWrapper from "../../helpers/fetchWrapper";
import {useSelector} from "react-redux";

const Discord = () => {

    const [servers, setServers] = useState([]);

    useEffect(() => {

            fetchWrapper.get('/api/discord-servers')
                .then(response => {
                        const data = response.data;
                        if (data.status === 'success') {
                            setServers(data.servers);
                        }
                    }
                ).catch(error => {
                setServers([]);
            });


    }, []);

    const columns = [
        {
            name: 'SERVER ID',
            selector: row => row.id,
            sortable: true,
        },
        {
            name: 'SERVER NAME',
            selector: row => row.name,
            sortable: true,
        },
        {
            name: 'ACTION',
            selector: row => <div>
                <Link to={`/discord-server/${row.id}`} className="btn btn-primary btn-sm">
                    <i className="fa fa-eye"></i>
                </Link>
            </div>,
        },
    ];

    return <>

        <DiscordInfo/>

        <CustomTable title="Discord Server Announcements" columns={columns} data={servers}/>
    </>
}

export default Discord;
