import React, {useEffect, useState} from "react";
import {Link, useParams} from "react-router-dom";
import CustomTable from "../../common-components/CustomTable";
import DiscordInfo from "./DiscordInfo";
import fetchWrapper from "../../helpers/fetchWrapper";
import {CFormSwitch} from "@coreui/react";
import {swalError} from "../../helpers/common";
import {useSelector} from "react-redux";

const DiscordServer = () => {

    const params = useParams();
    const id = params.id;
    const [channels, setChannels] = useState([]);
    const discordUser = useSelector(state => state.discordUser);

    const notificationToggle = (notification, channel) => {
        fetchWrapper.post('/api/notification', {
            server_id: channel.guild_id,
            channel_id: channel.id,
            last_message_id: channel.last_message_id,
            notification: notification
        }).then(response => {
            const data = response.data;
            const index = channels.findIndex(c => c.id === channel.id);
            if (data.status === 'success' && data.notification === true) {
                channels[index].notification = true;
            } else {
                channels[index].notification = false;
            }
            setChannels([...channels]);
        }).catch(error => {
            console.log(error);
            swalError('Error', 'Something went wrong');
        })
    }

    useEffect(() => {

            fetchWrapper.get('/api/discord-channels/'+id)
                .then(response => {
                        const data = response.data;
                        if (data.status === 'success') {
                            setChannels(data.channels);
                        }
                    }
                ).catch(error => {
                setChannels([]);
            });


    }, [discordUser]);

    const columns = [
        {
            name: 'CHANNEL ID',
            selector: row => row.id,
            sortable: true,
        },
        {
            name: 'CHANNEL NAME',
            selector: row => row.name,
            sortable: true,
        },
        {
            name: 'ACTIONS',
            selector: row => <div className="d-flex">
                <CFormSwitch style={{
                    width: '60px',
                    height: '30px',
                    cursor: 'pointer',
                }} size="xl" onChange={(e) => notificationToggle(e.target.checked, row)} checked={row.notification} />
                <Link to={`/discord-channel/${row.id}`} className="btn btn-primary btn-sm mx-2">
                    <i className="fa fa-eye"></i>
                </Link>
            </div>,
        },
    ];

    return <>

        <DiscordInfo/>

        <CustomTable title={<div className="d-flex justify-content-between">
            <span>Discord Server Announcements</span>
            <Link to="/discord" className="btn btn-primary btn-sm mx-2">Servers</Link>
        </div>} columns={columns} data={channels}/>
    </>;
}

export default DiscordServer;
